ARG coq_image="coqorg/coq:dev"
FROM ${coq_image}

WORKDIR /home/coq/mathcomp

COPY . .

RUN ["/bin/bash", "--login", "-c", "set -x \
  && opam switch \
  && eval $(opam env) \
  && opam repository add --all-switches --set-default coq-extra-dev https://coq.inria.fr/opam/extra-dev \
  && opam repository add --all-switches --set-default coq-core-dev https://coq.inria.fr/opam/core-dev \
  && opam update -y \
  && opam config list && opam repo list && opam list && coqc --version \
  && opam clean -a -c -s --logs \
  && sudo chown -R coq:coq /home/coq/mathcomp \
  && cd mathcomp \
  && make Makefile.coq \
  && make -f Makefile.coq -j ${NJOBS} all \
  && make -f Makefile.coq install \
  && make test-suite"]
