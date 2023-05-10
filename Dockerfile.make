ARG coq_image="coqorg/coq:dev"
# hadolint ignore=DL3006
FROM ${coq_image}

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
  && opam pin add -n -y -k path coq-mathcomp-ssreflect . \
  && opam install -y coq-mathcomp-ssreflect --deps-only \
  && opam config list && opam repo list && opam list && coqc --version \
  && opam clean -a -c -s --logs \
  && sudo chown -R coq:coq /home/coq/mathcomp \
  && make -C mathcomp Makefile.coq \
  && make -C mathcomp -f Makefile.coq -j "${NJOBS}" all \
  && make -C mathcomp -f Makefile.coq install \
  && make -C mathcomp test-suite

# Restore default shell to fully preserve backward compatibility
SHELL ["/bin/sh", "-c"]
# Still, we may remove this line later on.
