FROM ubuntu:21.10

ENV OPAMROOTISOK=1
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update
RUN apt-get install -y opam cvc4 z3 libgmp-dev dune proofgeneral

RUN opam init --auto-setup --disable-sandboxing
RUN opam repo add --all-switches coq-released https://coq.inria.fr/opam/released
RUN opam update
RUN opam install -y coq=8.13.2 coq-equations=1.3~beta1+8.13

RUN mkdir -p /opt/reviewer

RUN git clone https://github.com/jsarracino/mirrorsolve /opt/reviewer/mirrorsolve
WORKDIR /opt/mirrorsolve
RUN dune build && dune install

RUN mkdir -p /opt/reviewer/leapfrog
WORKDIR /opt/reviewer/leapfrog

ENTRYPOINT /bin/bash --rcfile /root/.profile
