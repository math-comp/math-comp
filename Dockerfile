ARG coq_image="rocq/rocq-prover:dev-ocaml-4.14"
# hadolint ignore=DL3006
FROM ${coq_image} as builder

ENV MATHCOMP_VERSION="dev"
ENV MATHCOMP_PACKAGE="rocq-mathcomp-group-representation"

WORKDIR /home/mathcomp

COPY . .

SHELL ["/bin/bash", "--login", "-o", "pipefail", "-c"]

# hadolint ignore=SC2046,DL3004
RUN set -x \
  && opam switch \
  && eval $(opam env) \
  && opam repository add --all-switches --set-default coq-extra-dev https://coq.inria.fr/opam/extra-dev \
  && opam repository add --all-switches --set-default coq-core-dev https://coq.inria.fr/opam/core-dev \
  && opam update -y \
  && opam config list && opam repo list && opam list \
  && if [ -d /home/coq ]; then sudo chown -R coq:coq /home/mathcomp; else sudo chown -R rocq:rocq /home/mathcomp; fi \
  && ( which rocq || opam install -y -v rocq-runtime ) \
  && rocq --version \
  && opam pin add -n -y -k path rocq-mathcomp-boot . \
  && opam pin add -n -y -k path rocq-mathcomp-order . \
  && opam pin add -n -y -k path rocq-mathcomp-finite-group . \
  && opam pin add -n -y -k path rocq-mathcomp-algebra . \
  && opam pin add -n -y -k path rocq-mathcomp-solvable . \
  && opam pin add -n -y -k path rocq-mathcomp-field . \
  && opam pin add -n -y -k path rocq-mathcomp-group-representation . \
  && opam install -y -v -j "${NJOBS}" "${MATHCOMP_PACKAGE}" \
  && opam clean -a -c -s --logs \
  && opam config list && opam list

# Restore default shell to fully preserve backward compatibility
SHELL ["/bin/sh", "-c"]
# Still, we may remove this line later on.
