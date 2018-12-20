ARG coq_image="coqorg/coq:dev"
FROM ${coq_image}

WORKDIR /home/coq/mathcomp

COPY . .

ARG compiler="base"
# other possible value: "edge"

RUN ["/bin/bash", "--login", "-c", "set -x \
  && declare -A switch_table \
  && switch_table=( [\"base\"]=\"${COMPILER}\" [\"edge\"]=\"${COMPILER_EDGE}\" ) \
  && opam_switch=\"${switch_table[${compiler}]}\" \
  && [ -n \"opam_switch\" ] \
  && opam switch set ${opam_switch} \
  && eval $(opam env) \
  && unset \"switch_table[${compiler}]\" \
  && for sw in \"${switch_table[@]}\"; do [ -n \"$sw\" ] && opam switch remove -y \"${sw}\"; done \
  && opam repository add --all-switches --set-default coq-extra-dev https://coq.inria.fr/opam/extra-dev \
  && opam repository add --all-switches --set-default coq-core-dev https://coq.inria.fr/opam/core-dev \
  && opam update -y \
  && opam config list && opam repo list && opam list && coqc --version \
  && opam clean -a -c -s --logs \
  && sudo chown -R coq:coq /home/coq/mathcomp \
  && cd mathcomp \
  && make Makefile.coq \
  && make -f Makefile.coq -j ${NJOBS} all \
  && make -f Makefile.coq install"]
