ARG BASE_IMAGE
FROM ${BASE_IMAGE}

# We need to be root to install system dependencies
USER root
RUN apt-get update && apt-get install -y \
    gawk git pkg-config libgmp-dev libmpfr-dev libunwind-dev autoconf \
    && rm -rf /var/lib/apt/lists/*

# We need to be root to install system dependencies,
# but opam usually runs as a user. Assuming the base image
# has a user 'opam', we switch to it.
USER opam
WORKDIR /home/opam/iris-tutorial

ARG OPAMYES=true
ENV OPAMROOTISOK=true
ARG MODE

# 3. Combined Opam Operation
# This is the "Magic" fix: Adding repos, updating, and installing in ONE step
# ensures the package solver doesn't use a stale cache.
RUN opam repo add rocq-released https://rocq-prover.org/opam/released --all --set-default && \
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --all --set-default && \
    opam update

# TODO: uncomment when vsrocq-language-server will start supporting ocaml 5.5
# RUN opam install -y -w vsrocq-language-server.2.4.3

# 4. Copy the opam file
COPY --chown=opam:opam iris-tutorial.opam .

# 5. Install Project Dependencies
RUN opam install . --deps-only -y

# 4. If mode is unstable, install the extra unstable package
RUN if [ "$MODE" = "unstable" ]; then \
    opam install -y rocq-iris-unstable; \
    fi

RUN echo "eval \$(opam env)" >> ~/.bashrc
