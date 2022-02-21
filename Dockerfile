FROM ubuntu:21.10
RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y opam cvc4 z3 libgmp-dev

RUN useradd -ms /bin/bash leapfrog
USER leapfrog
WORKDIR /home/leapfrog

RUN opam init --disable-sandboxing
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam update
RUN opam install -y coq=8.13.2 coq-equations=1.3~beta1+8.13

ENTRYPOINT /bin/bash
