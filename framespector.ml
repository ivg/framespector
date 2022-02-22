open Core_kernel
open Bap_main
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Graphlib.Std

module Analysis = Primus.Analysis
module Linker = Primus.Linker.Make(Analysis)
module Eval = Primus.Interpreter.Make(Analysis)
module Memory = Primus.Memory.Make(Analysis)

open Analysis.Syntax
open Analysis.Let

let max_frame_size = 4096

module Frame : sig
  type t
  type slot
  type prog

  val access : addr -> unit Analysis.t
  val change : addr -> unit Analysis.t
  val stored : addr -> unit Analysis.t
  val changed : t Primus.observation

  val size : t -> int
  val base : t -> addr
  val prog : t -> prog
  val slots : t -> slot list

  module Slot : sig
    val addr : slot -> addr
    val read : slot -> Size.t -> word list
  end

  module Prog : sig
    val start : prog -> addr
    val trace : prog -> Primus.pos list
  end
end = struct

  type info = {
    target : Theory.Target.t;
  }

  let is_big {target} =
    Theory.Endianness.(equal le) @@
    Theory.Target.endianness target

  module Slot = struct
    type t = {
      info : info;
      base : addr;
      data : word list;
    }

    let addr s = s.base
    let data s = s.data
    let read {data; info} size =
      let length = Size.in_bytes size in
      let concat = List.reduce_exn ~f:Word.concat in
      let is_big = is_big info in
      List.chunks_of ~length data |>
      List.map ~f:(fun chunk ->
          if is_big
          then concat chunk
          else Fn.compose concat List.rev chunk)
  end

  module Prog = struct
    type t = {
      start : addr;
      trace : Primus.Pos.t list;
    }
    let start p = p.start
    let trace p = List.rev p.trace
  end

  type slot = Slot.t
  type prog = Prog.t

  type t = {
    base : addr;
    size : int;
    info : info;
    data : slot list;
    prog : prog;
  }


  let base f = f.base
  let prog f = f.prog
  let slots f = f.data
  let size f = f.size

  let inspect_addr addr = Sexp.Atom (Addr.string_of_value addr)
  let inspect_size = sexp_of_int

  let inspect frame = Sexp.List [
      inspect_addr @@ frame.base;
      inspect_size @@ frame.size;
    ]

  let changed,was_changed =
    Primus.Observation.provide ~inspect "frame-changed"

  let state = Primus.Machine.State.declare
      ~uuid:"db67e5a2-2e36-479a-a656-74154ae46ed0"
      ~name:"framespector" @@ fun proj ->

    let target = Project.target proj in {
      base = Addr.data_addr target Bitvec.zero;
      size = Theory.Target.data_addr_size target / 8;
      data = [];
      info = {target};
      prog = {
        Prog.start = Addr.code_addr target Bitvec.zero;
        trace = []
      }
    }

  let foreach n ~f =
    List.init n ~f:ident |>
    Analysis.List.map ~f

  let read_slots {base; size; info={target}} =
    let slot_size = Theory.Target.data_addr_size target / 8 in
    foreach (size/slot_size) ~f:(fun slot ->
        let base = Addr.npred base (slot*slot_size) in
        let+ data = foreach slot_size ~f:(fun byte ->
            Memory.load (Addr.nsucc base byte)) in
        {Slot.info={target}; base; data})

  let update_prog frame =
    let* start = Eval.pc in
    let+ pos = Eval.pos in
    let trace =
      if Addr.equal frame.prog.start start
      then pos :: frame.prog.trace
      else [pos] in
    {Prog.start;trace}

  let was_changed frame =
    let* data = read_slots frame in
    let* prog = update_prog frame in
    let frame = {frame with data; prog} in
    Analysis.Local.put state frame >>= fun () ->
    Analysis.Observation.make was_changed frame

  let update f =
    let* () = Analysis.Local.update state ~f in
    let* frame = Analysis.Local.get state in
    if Word.is_zero frame.base
    then Analysis.return ()
    else was_changed frame

  let extent s base addr =
    if Addr.(addr < base)
    then min max_frame_size @@
      Addr.(to_int_exn @@ base - addr) +
      Theory.Target.data_addr_size s.info.target / 8
    else s.size

  let access addr = update @@ fun s ->
    if Word.is_zero addr then s
    else
      let base = Addr.max s.base addr in {
        s with base; size = max s.size (extent s base addr)
      }

  let stored addr =
    let* {base; size} as frame = Analysis.Local.get state in
    let endp = Addr.npred base size in
    if Addr.(addr <= base && addr >= endp)
    then was_changed frame
    else Analysis.return ()

  let change addr = update @@ fun s ->
    if Word.is_zero addr then s
    else
      let base = Addr.max s.base addr in {
        s with
        base;
        size = extent s base addr;
      }

  let size f = f.size

end

type Format.stag +=
  | File of {prev : string; curr : string; next : string}
  | Frame of Frame.t
  | Slot of Frame.slot * int
  | Addr of Addr.t
  | Data of string
  | Changed
  | Backref of int
  | Arg
  | Blk

let when_frame_pointer fps v k =
  if Set.mem fps v
  then k ()
  else Analysis.return ()

let variable_update fps (v,x) =
  when_frame_pointer fps v @@ fun () ->
  Frame.change (Primus.Value.to_word x)

let free_vars t =
  match Term.get_attr t Disasm.insn with
  | None -> Def.free_vars t
  | Some insn -> Bil.free_vars (Insn.bil insn)

let check_if_frame_based fps ptr =
  let* pos = Eval.pos in
  match pos with
  | Primus.Pos.Def {me} ->
    if Set.is_empty (Set.inter fps (free_vars me))
    then Analysis.return ()
    else Frame.access (Primus.Value.to_word ptr)
  | _ -> Analysis.return ()

let memory_update fps (ptr,_) =
  check_if_frame_based fps ptr >>= fun () ->
  Frame.stored (Primus.Value.to_word ptr)

let frame_pointers  =
  let+ target = Analysis.gets Project.target in
  Theory.Role.Register.[stack_pointer; frame_pointer] |>
  List.filter_map ~f:(Theory.Target.reg target) |>
  List.map ~f:Var.reify |>
  Set.of_list (module Var)

let with_level3 attr pos k =
  let get t = Term.get_attr t attr in
  match pos with
  | Primus.Pos.(Top _ | Sub _ | Arg _ | Blk _ ) -> ()
  | Phi {me; up={up={me=sub}}} ->
    k sub (get me)
  | Def {me; up={up={me=sub}}} ->
    k sub (get me)
  | Jmp {me; up={up={me=sub}}} ->
    k sub (get me)

let blocks proj =
  Project.disasm proj |>
  Disasm.cfg |>
  Graphs.Cfg.nodes |>
  Seq.map ~f:Block.addr |>
  Seq.fold ~f:Set.add
    ~init:Addr.Set.empty

let pp_pos ppf = function
  | Primus.Pos.Top _ -> Format.fprintf ppf "<sporadic>:"
  | Sub {me} -> Format.fprintf ppf "<%s>: (stub)" (Sub.name me)
  | Arg {up={me}} | Blk {up={me}} ->
    Format.fprintf ppf "<%s>:" (Sub.name me)
  | pos -> with_level3 Disasm.insn pos @@ fun sub insn ->
    match insn with
    | None ->
      Format.fprintf ppf "<%s>: (synthetic)"
        (Sub.name sub)
    | Some insn ->
      Format.fprintf ppf "<%s>: %a" (Sub.name sub)
        Insn.pp insn

type frames = {
  pending : Frame.t option;
  compare : Frame.t option;
  printed : int;
}

let state = Primus.Machine.State.declare
    ~uuid:"75d4f188-b3b8-4ad8-93aa-b22247678a5a"
    ~name:"pending-frame" @@ fun _ -> {
    pending=None;
    compare=None;
    printed=0
  }


module Inspectors = struct
  let selected = ref []
  let run ppf frame slot i =
    let opened =
      List.fold !selected ~init:0 ~f:(fun opened inspect ->
          match inspect frame slot i with
          | Some tag -> Format.pp_open_stag ppf tag; opened+1
          | None -> opened) in
    Fn.apply_n_times ~n:opened (Format.pp_close_stag ppf) ();
end

module Formats : sig
  val register : string -> (Format.formatter -> unit) -> unit
  val enable : string -> Format.formatter -> unit
end = struct
  let available = Hashtbl.create (module String)

  let register name enable =
    Hashtbl.add_exn available ~key:name ~data:enable

  let enable name ppf = match Hashtbl.find available name with
    | None -> invalid_argf "Unknown format %s" name ()
    | Some enable -> enable ppf
end

module Orgmode = struct
  let name = "orgmode"

  let pp_trace ppf = function
    | x :: _ -> pp_pos ppf x
    | _ -> ()

  let enable ppf =
    Format.pp_set_print_tags ppf true;
    Format.pp_set_mark_tags ppf false;
    let print_frame frame =
      let prog = Frame.prog frame in
      let pc = Frame.Prog.start prog in
      Format.fprintf ppf "* %s %a@\n"
        (Addr.string_of_value pc)
        pp_trace (Frame.Prog.trace prog) in
    let print_open_stag = function
      | Frame f -> print_frame f
      | Addr a -> Format.fprintf ppf "%s: " (Addr.string_of_value a)
      | Data s -> Format.fprintf ppf "%s@\n" s
      | _ -> () in
    Format.pp_set_formatter_stag_functions ppf {
      mark_open_stag = (fun _ -> "");
      mark_close_stag = (fun _ -> "");
      print_open_stag;
      print_close_stag=ignore;
    }

  let () = Formats.register name enable
end



let pp_byte ppf byte =
  Format.fprintf ppf "%02x" (Word.to_int_exn byte)

let hexdump bytes =
  List.map bytes ~f:(Format.asprintf "%a" pp_byte) |>
  String.concat ~sep:" "

let markup_frame ppf frame _before =
  let open Format in
  let with_tag x k =
    pp_open_stag ppf x;
    k ();
    pp_close_stag ppf () in
  with_tag (Frame frame) @@ fun () ->
  List.iteri (Frame.slots frame) ~f:(fun i slot ->
      with_tag (Slot (slot,i)) @@ fun () ->
      let base = Frame.Slot.addr slot in
      let data = hexdump@@Frame.Slot.read slot `r8 in
      with_tag (Addr base) ignore;
      with_tag (Data data) begin fun () ->
        Inspectors.run ppf frame slot i;
      end)

let queue_frame frame =
  Analysis.Local.update state ~f:(fun frames -> {
        frames with pending = Some frame
      })

let peek_frames {pending; compare} k =
  match pending,compare with
  | None,_ -> Analysis.return ()
  | Some frame,None -> k frame None
  | Some last,Some before -> k last (Some before)

let make_name prefix printed =
  Format.asprintf "%s-%04d.frame" prefix printed

let with_formatter prefix printed k = match prefix with
  | Some prefix ->
    let prev = make_name prefix (printed-1) in
    let curr = make_name prefix printed in
    let next = make_name prefix (printed+1) in
    Out_channel.with_file curr ~f:(fun out ->
        let ppf = Format.formatter_of_out_channel out in
        Format.pp_open_stag ppf (File {prev;curr;next});
        k ppf;
        Format.pp_close_stag ppf ();
        Format.pp_print_flush ppf ())
  | None ->
    k Format.std_formatter;
    Format.print_flush ()

let print_pending format prefix _ =
  let* frames = Analysis.Local.get state in
  peek_frames frames @@ fun pending previous ->
  Analysis.Local.put state {
    frames with
    pending = None;
    printed = frames.printed + 1
  } >>| fun () ->
  with_formatter prefix frames.printed @@ fun ppf ->
  Formats.enable format ppf;
  markup_frame ppf pending previous

let init format prefix =
  let* pointers = frame_pointers in
  Analysis.sequence Primus.Interpreter.[
      written >>> variable_update pointers;
      stored >>> memory_update pointers;
      Frame.changed >>> queue_frame;
      pc_change >>> print_pending format prefix;
    ]

let run start format prefix project =
  let system = Primus.System.Repository.get "stubbed-executor"
      ~package:"bap" in
  let state = Toplevel.current () in
  let init = init format prefix in
  let start = Linker.exec (`symbol start) in
  match Primus.System.run ~init ~start system project state
          ~args:[|"test"; "42"|] with
  | Ok (_, project, _) -> project
  | Error _ -> project

let start = Extension.Configuration.parameter
    Extension.Type.(string =? "_start") "start"

let prefix = Extension.Configuration.parameter
    Extension.Type.(some string) "paginate-prefix"
    ~doc:"If specified then the output each frame to a \
          separate file named $(b,PREFIX-xxxx.frame), where \
          $(b,xxxx) stands for the frame number"

let format = Extension.Configuration.parameter
    Extension.Type.(string =? "orgmode") "format"
    ~doc:"Print frames in the selected format"

let () = Extension.declare @@ fun ctxt ->
  let open Extension.Syntax in
  let start = ctxt-->start in
  let prefix = ctxt-->prefix in
  let format = ctxt-->format in
  Project.register_pass (run start format prefix);
  Ok ()
