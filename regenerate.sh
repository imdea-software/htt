#!/usr/bin/env bash

TMP=$(mktemp -d); git clone https://github.com/coq-community/templates.git $TMP
$TMP/generate.sh README.md coq-htt-core.opam dune-project

echo "Proceeding with customized generation..."

srcdir="templates-extra"

get_yaml() {
    # Arg 1: the meta.yml path
    # STDIN: the mustache code
    local meta="$1" temp
    temp=$(mktemp template-XXX)
    cat > "$temp"
    mustache "$meta" "$temp"
    rm -f -- "$temp"
}

for f in "$srcdir"/*.mustache; do
    target=$(basename "$f" .mustache)
    case "$target" in
        dune)
            mustache='{{ dune }}'
            bool=$(get_yaml meta.yml <<<"$mustache")
            if [ -n "$bool" ] && [ "$bool" != false ]; then
                mkdir -p -v htt && target="htt/$target"
            else
                continue
            fi
            ;;
        docker-action.yml)
            mustache='{{ action }}'
            bool=$(get_yaml meta.yml <<<"$mustache")
            if [ -n "$bool" ] && [ "$bool" != false ]; then
                mkdir -p -v .github/workflows && target=".github/workflows/$target"
            else
                continue
            fi
            ;;
    esac
    listed=false
    for specified_target in "$@"; do
        if [ "$specified_target" == "$target" ]; then
            listed=true
	fi
    done
    if [ $# -gt 0 ] && [ $listed != true ]; then
	continue
    fi
    echo "Generating $target..."
    mustache meta.yml "$f" > "$target"
done

