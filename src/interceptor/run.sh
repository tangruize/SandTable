#!/bin/sh

usage() {
  echo "$0 [-library LIBRARY_FILE] [-config CONFIG_FILE] COMMAND [ARGS]"
  exit 1
}

check() {
  if [ -n "$1" -a ! -r "$1" ]; then
    echo "Error: cannot read file \"$1\""
    exit 1
  fi
}

if [ -n "${MYSYSCALL_CONFIG}" ]; then
  export "MYSYSCALL_CONFIG=${MYSYSCALL_CONFIG}"
elif [ -n "${CONFIG}" ]; then
  export "MYSYSCALL_CONFIG=${CONFIG}"
fi

if [ -n "${LIBRARY}" ]; then
  LIBRARY="${LIBRARY}"
fi

while [ $(printf %.1s "$1") = "-" ]; do
  case "$1" in
  -c|-config|--config)
    export "MYSYSCALL_CONFIG=$2"
    shift 2
    ;;
  -l|-library|--library)
    LIBRARY="$2"
    shift 2
    ;;
  *)
    usage
    ;;
  esac
done

export PROGRAM_PATH="${PROGRAM_PATH:-1}"

if [ -z "$LIBRARY" ] || [ -z "$1" ]; then
  usage
fi

check "$LIBRARY"
check "$MYSYSCALL_CONFIG"

env "LD_PRELOAD=$LIBRARY" "$@"
