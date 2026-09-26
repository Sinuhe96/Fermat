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

# The package file is repo-tracked (it carries the chunk `lean_lib` wiring that
# makes `import Lk.Basic` resolve); sync it into the volume so the two copies
# cannot drift and a recreated volume regains the wiring.
if [ -f "$source_root/lakefile.toml" ]; then
  cp "$source_root/lakefile.toml" "$work_root/lakefile.toml"
fi

mkdir -p "$(dirname "$destination")"
cp "$source_file" "$destination"
cd "$work_root"

# Publish the module for consumer chunks (`import Lk.Basic`). `lean -o` writes
# the olean as a by-product of the compile we are already paying for; the
# previous olean is dropped first so that a FAILED compile cannot leave a stale
# artifact behind for a consumer to import.
olean="$work_root/.lake/build/lib/lean/${relative%.lean}.olean"
mkdir -p "$(dirname "$olean")"
rm -f "$olean"

exec lake env lean -o "$olean" "$relative"
