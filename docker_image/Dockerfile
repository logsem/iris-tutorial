ARG BASE_IMAGE
FROM ${BASE_IMAGE}

# We need to be root to install system dependencies
USER root
RUN apt-get update && apt-get install -y gawk git && rm -rf /var/lib/apt/lists/*

# We need to be root to install system dependencies,
# but opam usually runs as a user. Assuming the base image
# has a user 'opam', we switch to it.
USER opam
WORKDIR /home/opam/iris-tutorial

ARG OPAMYES=true
ENV OPAMROOTISOK=true
ARG MODE

# 1. Initialize repos
# With || true in case they already exist in the base image
RUN opam repo add --set-default rocq-released https://rocq-prover.org/opam/released || true
RUN opam repo add --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git || true

# 2. Copy the opam file from the project root (context is ..)
COPY --chown=opam:opam iris-tutorial.opam .

# 3. Update and Install dependencies from the .opam file
RUN opam update && \
    opam install . --deps-only -y && \
    opam install -y vsrocq-language-server

# 4. If mode is unstable, install the extra unstable package
RUN if [ "$MODE" = "unstable" ]; then \
    opam install -y rocq-iris-unstable; \
    fi

RUN echo "eval \$(opam env)" >> ~/.bashrc
