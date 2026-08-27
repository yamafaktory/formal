Search Mathlib before proving from scratch.

Most properties worth stating about a pure function are instances of something
Mathlib already proves. Rebuilding one by hand is the commonest way a proof gets
long, and Lean will not object: it type-checks, it is accepted, and it is still
the wrong artefact — slower to check every run, and tied to a shape of your
definition that the next edit to the source moves.

Ask before you write. `exact?` searches Mathlib for a term that closes the goal
and names what it finds; `apply?` does the same for a goal that still needs
arguments. Either is a proof worth submitting on its own: a search costs one Lean
run, which is what a guess costs too, and when it lands the check comes back
verified with the lemma named in the accepted proof.

formal runs that search for you, but only after your proof has already failed,
and only when the file holds one `:= by` with no further declaration after it. A
proof carrying its own helper lemmas is past what the recovery can rewrite, so
one that could have been a single line stays whatever you wrote. While you are
still looking for the lemma, keep the file to one theorem.

Then read what came back. An id listed under `recovered` was closed by something
other than what you sent, and GET /session/{id}/proof/{property_id} returns the
proof that was accepted and cached. Thirty lines of yours replaced by one `exact`
is the library telling you the property was already in it — take that lemma the
next time the shape comes up rather than reporting that your proof worked.

Length is not evidence of a hard property. Before submitting a long proof, check
that `simp`, `omega`, `decide` and `exact?` have each been tried against the bare
goal: a hand-rolled induction over a list that `List.filter_append` closes is a
defect in the proof, not a demonstration of effort.
