FROM binaryanalysisplatform/bap:latest as base

COPY --chown=opam:nogroup . /framespector/
WORKDIR /framespector
RUN eval $(opam env) && \
    bapbuild -pkg bap-primus framespector.plugin && \
    bapbundle install framespector.plugin

FROM ubuntu:18.04
RUN apt-get update && apt-get install libgmp-dev binutils --yes
COPY --from=base /home/opam/.opam/4.09/bin/bap /usr/bin/
COPY --from=base /home/opam/.opam/4.09/lib/bap/*.plugin /home/opam/.opam/4.09/lib/bap/
COPY --from=base /home/opam/.opam/4.09/share/bap /home/opam/.opam/4.09/share/bap
COPY --from=base /framespector/examples/ /examples
RUN cp /examples/test /artifact
CMD ["bap", "disassemble", "/artifact", "--pass=framespector"]
