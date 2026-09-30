#!/bin/sh
set -eu

fail() {
    echo "release: $*" >&2
    exit 1
}

usage="usage: scripts/release.sh [--yes] <version>, e.g. 1.1.0"
yes=
version=
for arg in "$@"; do
    case "$arg" in
        -y | --yes) yes=1 ;;
        -*) fail "$usage" ;;
        *) [ -z "$version" ] || fail "$usage"; version="${arg#v}" ;;
    esac
done
[ -n "$version" ] || fail "$usage"
tag="v$version"
echo "$version" | grep -Eq '^[0-9]+\.[0-9]+\.[0-9]+$' || fail "$version is not MAJOR.MINOR.PATCH"

root=$(git rev-parse --show-toplevel)
cd "$root"

[ "$(git branch --show-current)" = "main" ] || fail "not on main"
[ -z "$(git status --porcelain)" ] || fail "the working tree is not clean"
git fetch -q origin main --tags
[ "$(git rev-parse HEAD)" = "$(git rev-parse origin/main)" ] || fail "main is not at origin/main"
git rev-parse -q --verify "refs/tags/$tag" >/dev/null && fail "$tag already exists"

current=$(sed -n 's/^version = "\(.*\)"$/\1/p' rust/Cargo.toml)
if [ "$current" != "$version" ]; then
    sed -i.bak "s/^version = \"$current\"$/version = \"$version\"/" rust/Cargo.toml
    rm rust/Cargo.toml.bak
    (cd rust && cargo update -q --workspace --offline)
    git add rust/Cargo.toml rust/Cargo.lock
    git commit -q -m "Release $tag"
    echo "release: bumped $current -> $version"
fi

git tag -a "$tag" -m "formal $version"
echo "release: tagged $tag at $(git rev-parse --short HEAD)"

if [ -n "$yes" ]; then
    answer=y
else
    printf 'release: push main and %s to origin? [y/N] ' "$tag"
    read -r answer || answer=
    [ -n "$answer" ] || echo
fi
case "$answer" in
    y | Y) ;;
    *)
        echo "release: nothing pushed. To undo: git tag -d $tag"
        [ "$current" != "$version" ] && echo "release: and git reset --hard origin/main"
        exit 0
        ;;
esac

[ "$current" != "$version" ] && git push -q origin main
git push -q origin "$tag"
echo "release: pushed; follow it with gh run watch \$(gh run list --workflow release.yml --limit 1 --json databaseId -q '.[0].databaseId')"
