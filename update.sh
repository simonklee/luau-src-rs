#!/bin/sh

set -eu

usage() {
    echo "Usage: $0 [--dry-run] [REF]"
    echo "Update Luau from simonklee/luau (default ref: master): the sources, and the"
    echo "version's build metadata in Cargo.toml (luau<release>.sk.<commit>)."
    echo "REF is a branch, a tag or a full commit id. LUAU_REPOSITORY overrides the"
    echo "repository (a URL or a local path)."
}

die() {
    echo "error: $*" >&2
    exit 1
}

ref=master
ref_set=false
dry_run=false
for arg in "$@"; do
    case "$arg" in
        --dry-run) dry_run=true ;;
        -h|--help) usage; exit 0 ;;
        -*) die "unknown option: $arg" ;;
        *)
            [ "$ref_set" = false ] || die "expected at most one ref"
            ref=$arg
            ref_set=true
            ;;
    esac
done

cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repository=${LUAU_REPOSITORY:-https://github.com/simonklee/luau.git}
components="Ast Bytecode CodeGen Common Compiler Config Inliner Require VM"
set --
for component in $components; do
    set -- "$@" "luau/$component"
done
changes=$(git status --porcelain --untracked-files=all --ignored -- Cargo.toml "$@")
[ -z "$changes" ] ||
    die "commit or stash changes and move ignored files out of vendored components first"

temporary=$(mktemp -d "${TMPDIR:-/tmp}/luau-update.XXXXXX")
# The new manifest is written next to the old one, so that installing it is a rename.
staged=.Cargo.toml.update
replaced=
cleanup() {
    status=$?
    trap - 0 HUP INT TERM
    if [ -n "$replaced" ]; then
        echo "Update interrupted; restoring previous sources." >&2
        for component in $replaced; do
            rm -rf "luau/$component" &&
                cp -R "$temporary/backup/$component" "luau/$component" || {
                    echo "Restore failed; backup retained at $temporary/backup" >&2
                    exit 1
                }
        done
    fi
    rm -f "$staged"
    rm -rf "$temporary"
    exit "$status"
}
trap cleanup 0
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

echo "Fetching $repository ($ref)..."
git init --quiet "$temporary/source"
git -C "$temporary/source" fetch --quiet --depth=100 "$repository" "$ref"
commit=$(git -C "$temporary/source" rev-parse --verify 'FETCH_HEAD^{commit}')
short=$(git -C "$temporary/source" rev-parse --short=8 "$commit")
# The fork has no release tags. Upstream syncs are merged, so take the latest
# release sync anywhere in the fetched history.
git -C "$temporary/source" log --format=%s "$commit" > "$temporary/history"
version=$(sed -n 's|^Sync to upstream/release/\([0-9][0-9]*\)\([[:space:]].*\)\{0,1\}$|\1|p' "$temporary/history" | sort -n | sed -n '$p')
[ -n "$version" ] || die "no Luau release sync found in the fetched 100 commits"
git -C "$temporary/source" checkout --quiet "$commit" -- $components
for component in $components; do
    for part in include src; do
        [ -d "$temporary/source/$component/$part" ] ||
            die "missing upstream directory: $component/$part"
    done
done

current=$(sed -n 's|^version = "\([0-9.]*\)+.*"$|\1|p' Cargo.toml)
[ -n "$current" ] || die "no version in Cargo.toml"
crate_version="$current+luau$version.sk.$short"
echo "Luau 0.$version at $commit: luau0-src $crate_version"
grep -q "^version = \"$current+luau$version[.\"]" Cargo.toml ||
    echo "note: the Luau release changed; set the crate's major.minor to match mlua-sys" >&2
if [ "$dry_run" = true ]; then
    echo "Dry run: sources were not changed."
    exit 0
fi

# Stage and validate before replacing anything; preserve Custom and local files.
sed "s|^version = \"[^\"]*\"$|version = \"$crate_version\"|" Cargo.toml > "$staged"
mkdir "$temporary/backup"
for component in $components; do
    cp -R "luau/$component" "$temporary/backup/$component"
done
for component in $components; do
    replaced="$replaced $component"
    rm -rf "luau/$component"
    cp -R "$temporary/source/$component" "luau/$component"
done
# The sources and the manifest change together: a failed rename restores the sources.
trap '' HUP INT TERM
mv -f "$staged" Cargo.toml
replaced=

echo "Done."
