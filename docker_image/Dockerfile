ARG BASE_IMAGE
FROM ${BASE_IMAGE}

RUN opam repo add rocq-released https://rocq-prover.org/opam/released --all --set-default && \
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --all --set-default && \
    opam update

COPY --from=repo iris-tutorial.opam .
RUN opam install . --deps-only -y && \
    opam install -y rocq-iris-unstable

# TODO: uncomment when vsrocq-language-server will start supporting ocaml 5.5
# RUN opam install -y -w vsrocq-language-server

RUN echo "eval \$(opam env)" >> ~/.bashrc
