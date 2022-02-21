open Core_kernel
open Bap_main
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Graphlib.Std

module Analysis = Primus.Analysis
open Analysis.Syntax
open Analysis.Let

let max_frame_size = 4096

module Frame : sig
  type t
  val access : addr -> unit Analysis.t
  val change : addr -> unit Analysis.t
  val stored : addr -> unit Analysis.t
  val changed : t Primus.observation
  val content : t -> (addr * string) list Analysis.t
end = struct
  module Memory = Primus.Memory.Make(Analysis)

  type info = {
    target : Theory.Target.t;
    blocks : Addr.Set.t;
  }

  type t = {
    base : addr;
    size : int;
    info : info;
  }

  let blocks proj =
    Project.disasm proj |>
    Disasm.cfg |>
    Graphs.Cfg.nodes |>
    Seq.map ~f:Block.addr |>
    Seq.fold ~f:Set.add
      ~init:Addr.Set.empty

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
      info = {target; blocks = blocks proj};
    }

  let update f =
    let* () = Analysis.Local.update state ~f in
    let* frame = Analysis.Local.get state in
    if Word.is_zero frame.base
    then Analysis.return ()
    else Analysis.Observation.make was_changed frame

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
    then Analysis.Observation.make was_changed frame
    else Analysis.return ()

  let change addr = update @@ fun s ->
    if Word.is_zero addr then s
    else
      let base = Addr.max s.base addr in {
        s with
        base;
        size = extent s base addr;
      }

  let foreach n ~f =
    List.init n ~f:ident |>
    Analysis.List.map ~f

  let pp_byte ppf byte =
    Format.fprintf ppf "%02x" (Word.to_int_exn byte)

  let hexdump bytes =
    List.map bytes ~f:(Format.asprintf "%a" pp_byte) |>
    String.concat ~sep:" "

  let content {base; size; info={target}} =
    let slot_size = Theory.Target.data_addr_size target / 8 in
    foreach (size/slot_size) ~f:(fun slot ->
        let base = Addr.npred base (slot*slot_size) in
        let+ bytes = foreach slot_size ~f:(fun byte ->
            Memory.load (Addr.nsucc base byte)) in
        base,hexdump bytes)
end

module Linker = Primus.Linker.Make(Analysis)
module Eval = Primus.Interpreter.Make(Analysis)

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
  pending : string option;
  printed : int;
}

let frames = Primus.Machine.State.declare
    ~uuid:"75d4f188-b3b8-4ad8-93aa-b22247678a5a"
    ~name:"pending-frame" @@ fun _ -> {pending=None; printed=0}


let queue_frame frame =
  let* content = Frame.content frame in
  let* pc = Eval.pc in
  let* pos = Eval.pos in
  let buf = Buffer.create 64 in
  let ppf = Format.formatter_of_buffer buf in
  Format.fprintf ppf "* %s %a@\n" (Addr.string_of_value pc) pp_pos pos;
  List.iter content ~f:(fun (addr,data) ->
      Format.fprintf ppf "%s: %s@\n"
        Addr.(string_of_value addr) data);
  Format.pp_print_flush ppf ();
  let frame = Buffer.contents buf in
  Analysis.Local.update frames ~f:(fun frames ->
      {frames with pending=Some frame})

let print_pending prefix _ =
  let* {pending; printed} = Analysis.Local.get frames in
  match pending with
  | None -> Analysis.return ()
  | Some pending ->
    Analysis.Local.put frames {
      pending = None;
      printed = printed + 1
    } >>| fun () ->
    match prefix with
    | Some prefix ->
      let filename = Format.asprintf "%s-%04d.frame" prefix printed in
      Out_channel.with_file filename ~f:(fun out ->
          fprintf out "%s\n" pending);
    | None -> printf "%s\n" pending

let init prefix =
  let* pointers = frame_pointers in
  Analysis.sequence Primus.Interpreter.[
      written >>> variable_update pointers;
      stored >>> memory_update pointers;
      Frame.changed >>> queue_frame;
      pc_change >>> print_pending prefix;
    ]

let run start prefix project =
  let system = Primus.System.Repository.get "stubbed-executor"
      ~package:"bap" in
  let state = Toplevel.current () in
  let init = init prefix in
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

let () = Extension.declare @@ fun ctxt ->
  let start = Extension.Configuration.get ctxt start in
  let prefix = Extension.Configuration.get ctxt prefix in
  Project.register_pass (run start prefix);
  Ok ()
