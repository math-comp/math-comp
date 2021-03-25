#!/usr/bin/env bash

mkdir -p .theia
echo "{ \"coqtop.binPath\": \"$(dirname $(which coqtop))\" }" > .theia/settings.json
