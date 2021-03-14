#!/usr/bin/env bash

mkdir -p .theia
echo "{ \"coqtop.binPath\": \"$COQBIN\" }" > .theia/settings.json
