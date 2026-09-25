#!/bin/sh
set -eu

case "${1-}" in
  "") set -- ;;
  --full) ;;
  *)
    echo "usage: $0 [--full]" >&2
    exit 2
    ;;
esac

exec python /workspace/pipeline/smoke/smoke_pipeline.py "$@"
