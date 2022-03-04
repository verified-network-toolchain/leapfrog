FROM ocaml/opam:ubuntu-21.10-ocaml-4.12

ENV DEBIAN_FRONTEND=noninteractive
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8

ENV LEAPFROG_APT_DEPS \
    cvc4 \
    z3 \
    python3.10 \
    pipenv \
    time

ENV LEAPFROG_OPAM_DEPS \
    coq=8.13.2 \
    coq-equations=1.3~beta1+8.13 \
    dune=2.9.3

ENV COQ_REPO=https://coq.inria.fr/opam/released 


RUN sudo apt-get update && \
    sudo apt-get install -y $LEAPFROG_APT_DEPS && \
    sudo ln -s /usr/bin/python3.10 /usr/bin/python

RUN opam repo add --all-switches coq-released $COQ_REPO && \
    opam update && \
    opam install -y $LEAPFROG_OPAM_DEPS

RUN git clone https://github.com/jsarracino/mirrorsolve /home/opam/mirrorsolve
RUN opam install -y /home/opam/mirrorsolve

COPY --chown=opam:opam . /home/opam/leapfrog
WORKDIR /home/opam/leapfrog
RUN opam install -y . --deps-only
RUN . ~/.profile && make build pipenv

ENTRYPOINT /bin/bash --login -i
