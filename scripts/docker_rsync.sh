#!/bin/bash

set -e

if test -f /.dockerenv; then
    echo Should not run inside docker
    exit
fi

PROJECT_DIR=$(realpath "$(dirname "$(realpath "$0")")"/..)

cd "$PROJECT_DIR"
mkdir -p build/mount
rsync -av --exclude='*.toolbox' --exclude='__pycache__' --exclude='model' --exclude='build' --exclude='config.txt' \
    ./src ./scripts ./systems Makefile Makefile.inc build/mount
