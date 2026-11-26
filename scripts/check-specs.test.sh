#!/bin/sh
set -u

here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
failures=0

fail() {
    echo "check-specs test: $*" >&2
    failures=$((failures + 1))
}

cat >"$work/formal" <<'STUB'
#!/bin/sh
spec=$2
shift 2
inputs=
answers=
while [ $# -gt 0 ]; do
    case "$1" in
        --inputs) inputs=$2; shift ;;
        --answers) answers=$2; shift ;;
    esac
    shift
done
case "$spec" in
    refused.lean) echo "refused: no such spec" >&2; exit 2 ;;
esac
if [ -n "$inputs" ]; then
    case "$spec" in
        compares.lean) echo '{"F": [1]}' >"$inputs" ;;
        *) echo '{}' >"$inputs" ;;
    esac
    exit 1
fi
echo "report of $spec"
[ -z "$answers" ] || cat "$answers"
case "$spec" in
    failing.lean) exit 1 ;;
esac
exit 0
STUB
chmod +x "$work/formal"

run() {
    : >"$work/summary.md"
    : >"$work/answered"
    FORMAL_BIN="$work/formal" FORMAL_SPECS="$1" GITHUB_STEP_SUMMARY="$work/summary.md" \
        FORMAL_ANSWERS_COMMAND="${2:-}" "$here/check-specs.sh" >"$work/out.txt" 2>&1
}

dollar='$'
answer="echo \"${dollar}FORMAL_SPEC\" >>$work/answered; echo '{\"F\": [1]}' >\"${dollar}FORMAL_ANSWERS\""

run "plain.lean compares.lean" "$answer" || fail "a passing run exits $?"
[ "$(cat "$work/answered")" = "compares.lean" ] || fail "the answers ran for: $(cat "$work/answered")"
grep -q '{"F": \[1\]}' "$work/out.txt" || fail "the answers did not reach formal"
[ "$(grep -c '^### ' "$work/summary.md")" -eq 2 ] || fail "the summary misses a spec"

run "plain.lean failing.lean" && fail "a failing spec passes"

run "refused.lean plain.lean" && fail "a refused spec passes"
grep -q "refused: no such spec" "$work/summary.md" || fail "the summary misses the refusal"

run "compares.lean" "exit 3" && fail "a failing answers command passes"
grep -q "compares.lean" "$work/summary.md" || fail "the summary misses the failed answers"

rm -rf "$work"
[ "$failures" -eq 0 ] || exit 1
echo "check-specs test: ok"
