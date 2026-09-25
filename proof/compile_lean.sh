#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: $0 <relative-path-under-pipeline/03-lean>" >&2
  exit 2
fi

relative=$1
case "$relative" in
  *.lean) ;;
  *)
    echo "path must end in .lean" >&2
    exit 2
    ;;
esac
case "$relative" in
  /*|*..*)
    echo "absolute paths and '..' are not allowed" >&2
    exit 2
    ;;
esac

source_root=/workspace/pipeline/03-lean
work_root=/workspace/work/testproj
source_file=$source_root/$relative
destination=$work_root/$relative

if [ ! -f "$source_file" ]; then
  echo "missing Lean source: $source_file" >&2
  exit 2
fi
if [ ! -f "$work_root/lakefile.toml" ] || [ ! -f "$work_root/lean-toolchain" ]; then
  echo "Lake project is not initialized: $work_root" >&2
  exit 1
fi

mkdir -p "$(dirname "$destination")"
cp "$source_file" "$destination"
cd "$work_root"
exec lake env lean "$relative"
