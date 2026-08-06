#!/usr/bin/env bash

# Fix the Rocq dependencies that coq-community/templates cannot currently
# express. Run this after regenerating the repository files from meta.yml.

set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
opam_file=${1:-"${script_dir}/coq-htt.opam"}

if [[ ! -f ${opam_file} ]]; then
  echo "error: opam file not found: ${opam_file}" >&2
  exit 1
fi

dependency_count() {
  local package=$1
  awk -v package="${package}" '
    $0 ~ "^[[:space:]]*\"" package "\"[[:space:]]*($|\\{)" {
      count++
    }
    END {
      print count + 0
    }
  ' "${opam_file}"
}

coq_count=$(dependency_count coq)
rocq_core_count=$(dependency_count rocq-core)
rocq_stdlib_count=$(dependency_count rocq-stdlib)

if (( coq_count == 0 && rocq_core_count == 1 && rocq_stdlib_count == 1 )); then
  echo "Rocq dependencies are already patched in ${opam_file}"
  exit 0
fi

if (( coq_count != 1 || rocq_core_count != 0 || rocq_stdlib_count != 0 )); then
  echo "error: unexpected Rocq dependency layout in ${opam_file}" >&2
  echo "       expected one coq dependency and no rocq-core/rocq-stdlib dependencies" >&2
  echo "       found coq=${coq_count}, rocq-core=${rocq_core_count}, rocq-stdlib=${rocq_stdlib_count}" >&2
  exit 1
fi

temporary_file=$(mktemp "${opam_file}.tmp.XXXXXX")
trap 'rm -f -- "${temporary_file}"' EXIT
cp -p -- "${opam_file}" "${temporary_file}"

awk '
  /^[[:space:]]*"coq"[[:space:]]*($|\{)/ {
    dependency = $0
    sub(/"coq"/, "\"rocq-core\"", dependency)
    print dependency

    match($0, /^[[:space:]]*/)
    indentation = substr($0, RSTART, RLENGTH)
    print indentation "\"rocq-stdlib\""
    patched++
    next
  }
  {
    print
  }
  END {
    if (patched != 1) {
      exit 1
    }
  }
' "${opam_file}" > "${temporary_file}"

if command -v opam >/dev/null 2>&1; then
  opam lint "${temporary_file}"
fi

mv -- "${temporary_file}" "${opam_file}"
trap - EXIT

echo "Patched ${opam_file}: coq -> rocq-core; added rocq-stdlib"
