FROM ryosusato/mochi-env:latest
USER opam
WORKDIR /home/opam

COPY --chown=opam:opam . .

RUN eval $(opam env) && \
    dune build && \
    ./src/mochi.exe -v
