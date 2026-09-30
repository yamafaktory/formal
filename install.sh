#!/bin/sh
set -eu

repo="yamafaktory/formal"
install_dir="${FORMAL_INSTALL_DIR:-$HOME/.local/bin}"
version="${FORMAL_VERSION:-latest}"

fail() {
    echo "formal: $*" >&2
    exit 1
}

case "$(uname -s)" in
    Linux) os="unknown-linux-musl" ;;
    Darwin) os="apple-darwin" ;;
    *) fail "no prebuilt binary for $(uname -s); use cargo install --git https://github.com/$repo formal-cli" ;;
esac

case "$(uname -m)" in
    x86_64 | amd64) arch="x86_64" ;;
    aarch64 | arm64) arch="aarch64" ;;
    *) fail "no prebuilt binary for $(uname -m); use cargo install --git https://github.com/$repo formal-cli" ;;
esac

if [ "$os" = "apple-darwin" ] && [ "$arch" = "x86_64" ] &&
    [ "$(sysctl -n sysctl.proc_translated 2>/dev/null || echo 0)" = "1" ]; then
    arch="aarch64"
fi

archive="formal-$arch-$os.tar.gz"
if [ "$version" = "latest" ]; then
    base="https://github.com/$repo/releases/latest/download"
else
    base="https://github.com/$repo/releases/download/$version"
fi

command -v curl >/dev/null || fail "curl is required"
command -v tar >/dev/null || fail "tar is required"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

echo "formal: downloading $archive ($version)"
curl --proto '=https' --tlsv1.2 -fsSL "$base/$archive" -o "$tmp/$archive" ||
    fail "download failed: $base/$archive"
curl --proto '=https' --tlsv1.2 -fsSL "$base/$archive.sha256" -o "$tmp/$archive.sha256" ||
    fail "download failed: $base/$archive.sha256"

expected=$(cut -d ' ' -f 1 "$tmp/$archive.sha256")
if command -v sha256sum >/dev/null; then
    actual=$(sha256sum "$tmp/$archive" | cut -d ' ' -f 1)
elif command -v shasum >/dev/null; then
    actual=$(shasum -a 256 "$tmp/$archive" | cut -d ' ' -f 1)
else
    fail "sha256sum or shasum is required to verify the download"
fi
[ "$expected" = "$actual" ] || fail "checksum mismatch for $archive"

tar -xzf "$tmp/$archive" -C "$tmp"
mkdir -p "$install_dir"
mv "$tmp/formal" "$install_dir/formal"
chmod 755 "$install_dir/formal"

echo "formal: installed to $install_dir/formal"
case ":$PATH:" in
    *":$install_dir:"*) ;;
    *) echo "formal: $install_dir is not on your PATH; add it" ;;
esac
echo "formal: next, run formal setup"
