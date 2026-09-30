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

confirm() {
    if [ -n "$yes" ]; then
        return 0
    fi
    printf 'release: %s? [y/N] ' "$1"
    read -r answer || answer=
    [ -n "$answer" ] || echo
    case "$answer" in
        y | Y) return 0 ;;
        *) return 1 ;;
    esac
}

current=$(sed -n 's/^version = "\(.*\)"$/\1/p' rust/Cargo.toml)
if [ "$current" != "$version" ]; then
    branch="release-$tag"
    git switch -q -c "$branch"
    sed -i.bak "s/^version = \"$current\"$/version = \"$version\"/" rust/Cargo.toml
    rm rust/Cargo.toml.bak
    (cd rust && cargo update -q --workspace --offline)
    git add rust/Cargo.toml rust/Cargo.lock
    git commit -q -m "Release $tag"
    echo "release: bumped $current -> $version on $branch"
    if ! confirm "push $branch and open a pull request"; then
        echo "release: nothing pushed. To undo: git switch main && git branch -D $branch"
        exit 0
    fi
    git push -q -u origin "$branch"
    gh pr create --title "Release $tag" --body "Bumps the workspace version to $version. Once merged, run scripts/release.sh $version on main to tag it."
    echo "release: once it merges, run scripts/release.sh $version on main to tag it"
    exit 0
fi

git tag -a "$tag" -m "formal $version"
echo "release: tagged $tag at $(git rev-parse --short HEAD)"
if ! confirm "push $tag to origin"; then
    echo "release: nothing pushed. To undo: git tag -d $tag"
    exit 0
fi
git push -q origin "$tag"
echo "release: pushed; follow it with gh run watch \$(gh run list --workflow release.yml --limit 1 --json databaseId -q '.[0].databaseId')"
