ARG coq_image="rocq/rocq-prover:dev-ocaml-4.14"
# hadolint ignore=DL3006
FROM ${coq_image}

# TODO: update this when 9.0.0 goes live
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
  && opam pin add -n -y -k path rocq-mathcomp-ssreflect . \
  && opam install -y rocq-mathcomp-ssreflect --deps-only \
  && opam config list && opam repo list && opam list && coqc --version \
  && opam clean -a -c -s --logs \
  && sudo chown -R coq:coq /home/coq/mathcomp \
  && make Makefile.coq \
  && make -f Makefile.coq -j "${NJOBS}" all \
  && make -f Makefile.coq install \
  && make test-suite

# Restore default shell to fully preserve backward compatibility
SHELL ["/bin/sh", "-c"]
# Still, we may remove this line later on.
