#!/usr/bin/env bash

mkdir -p .vscode
echo "{ \"coqtop.binPath\": \"$(dirname $(which coqtop))\" }" > .vscode/settings.json
