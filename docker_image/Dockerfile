FROM debian:bookworm

RUN apt-get -y update
RUN apt-get -y upgrade
RUN apt-get -y install make gcc patch git unzip bubblewrap curl libgmp-dev bzip2 pkg-config gawk

ARG OPAMYES=true
ENV OPAMROOTISOK=true

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
RUN opam install coq.8.20.1 vscoq-language-server
RUN opam install coq-iris.4.3.0 coq-iris-heap-lang

RUN opam switch create unstable ocaml.5.2.0
RUN eval $(opam env)
RUN opam update
RUN opam install coq.8.20.1 vscoq-language-server
RUN opam install coq-iris coq-iris-heap-lang coq-iris-unstable

RUN opam switch stable
RUN eval $(opam env)
RUN opam update

RUN echo 'eval $(opam env)' >> ~/.bashrc
