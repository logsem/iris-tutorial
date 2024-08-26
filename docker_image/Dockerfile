FROM debian:bookworm

RUN apt-get update && apt-get -y upgrade && apt-get -y install make gcc patch git unzip bubblewrap curl libgmp-dev bzip2

ARG OPAMYES=true OPAMROOTISOK=true

RUN curl -sL https://github.com/ocaml/opam/releases/download/2.2.1/opam-2.2.1-x86_64-linux -o opam
RUN install opam /usr/local/bin/opam
RUN rm -rf opam

RUN opam init
RUN eval $(opam env)
RUN opam repo add --set-default coq-released https://coq.inria.fr/opam/released
RUN opam repo add --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git

RUN opam switch create stable ocaml.5.2.0
RUN eval $(opam env)
RUN opam update
RUN opam install coq.8.19.2 coq-iris.4.2.0 coq-iris-heap-lang vscoq-language-server

RUN opam switch create unstable ocaml.5.2.0
RUN eval $(opam env)
RUN opam update
RUN opam install coq.8.19.2 coq-iris coq-iris-heap-lang coq-iris-unstable vscoq-language-server

RUN opam switch stable
RUN opam update
RUN eval $(opam env)

RUN echo 'eval $(opam env)' >> ~/.bashrc