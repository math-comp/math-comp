ARG coq_image="coqorg/coq:dev"
FROM ${coq_image} as builder

WORKDIR /home/coq/mathcomp

COPY . .

RUN ["/bin/bash", "--login", "-c", "set -x \
  && [ -n \"${COMPILER_EDGE}\" ] \
  && opam switch set \"${COMPILER_EDGE}\" \
  && eval $(opam env) \
  && [ -n \"${COMPILER}\" ] \
  && opam switch remove -y \"${COMPILER}\" \
  && opam repository add --all-switches --set-default coq-extra-dev https://coq.inria.fr/opam/extra-dev \
  && opam repository add --all-switches --set-default coq-core-dev https://coq.inria.fr/opam/core-dev \
  && opam update -y \
  && opam config list && opam repo list && opam list && coqc --version \
  && sudo chown -R coq:coq /home/coq/mathcomp \
  && opam pin add -n -k path coq-mathcomp-ssreflect . \
  && opam pin add -n -k path coq-mathcomp-fingroup . \
  && opam pin add -n -k path coq-mathcomp-algebra . \
  && opam pin add -n -k path coq-mathcomp-solvable . \
  && opam pin add -n -k path coq-mathcomp-field . \
  && opam pin add -n -k path coq-mathcomp-character . \
  && opam install -y -v -j ${NJOBS} coq-mathcomp-character \
  && opam clean -a -c -s --logs"]

FROM coqorg/base:bare

ENV COMPILER=""
ENV MATHCOMP_VERSION="dev"
ENV MATHCOMP_PACKAGE="coq-mathcomp-character"

COPY --from=builder --chown=coq:coq /home/coq/.opam /home/coq/.opam
COPY --from=builder --chown=coq:coq /home/coq/.profile /home/coq/.profile
