#!/bin/sh
set -u

specs="${FORMAL_SPECS:?name the specs to check in FORMAL_SPECS}"
formal="${FORMAL_BIN:-formal}"
proofs="${FORMAL_PROOFS:-proofs}"
summary="${GITHUB_STEP_SUMMARY:-/dev/null}"
scratch=$(mktemp -d)
report="$scratch/report.txt"
tick='`'
failed=0

publish() {
    cat "$report"
    {
        printf '### %s\n\n%s\n' "$tick$1$tick" "$tick$tick$tick"
        cat "$report"
        printf '%s\n\n' "$tick$tick$tick"
    } >>"$summary"
}

for spec in $specs; do
    set -- check "$spec" --proofs "$proofs"
    if [ -n "${FORMAL_ANSWERS_COMMAND:-}" ]; then
        export FORMAL_SPEC="$spec"
        export FORMAL_INPUTS="$scratch/inputs.json"
        export FORMAL_ANSWERS="$scratch/answers.json"
        rm -f "$FORMAL_INPUTS" "$FORMAL_ANSWERS"
        "$formal" "$@" --inputs "$FORMAL_INPUTS" >"$report" 2>&1
        if [ $? -eq 2 ]; then
            publish "$spec"
            failed=1
            continue
        fi
        if [ "$(cat "$FORMAL_INPUTS")" != "{}" ]; then
            if ! sh -c "$FORMAL_ANSWERS_COMMAND" >"$report" 2>&1; then
                echo "formal: the answers command failed for $spec" >>"$report"
                publish "$spec"
                failed=1
                continue
            fi
            set -- "$@" --answers "$FORMAL_ANSWERS"
        fi
    fi
    "$formal" "$@" >"$report" 2>&1
    status=$?
    publish "$spec"
    [ "$status" -eq 0 ] || failed=1
done

exit "$failed"
