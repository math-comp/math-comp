ARG coq_image="coqorg/coq:dev"
# hadolint ignore=DL3006
FROM ${coq_image} as builder

ENV MATHCOMP_VERSION="dev"
ENV MATHCOMP_PACKAGE="coq-mathcomp-character"

WORKDIR /home/coq/mathcomp

COPY . .

SHELL ["/bin/bash", "--login", "-o", "pipefail", "-c"]

# hadolint ignore=SC2046,DL3004
RUN set -x \
  && opam switch \
  && eval $(opam env) \
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
  && opam install -y -v -j "${NJOBS}" "${MATHCOMP_PACKAGE}" \
  && opam clean -a -c -s --logs \
  && opam config list && opam list

# Restore default shell to fully preserve backward compatibility
SHELL ["/bin/sh", "-c"]
# Still, we may remove this line later on.
