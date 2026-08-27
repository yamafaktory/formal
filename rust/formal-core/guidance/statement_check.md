Read the statement back before you submit.

Lean accepts a proof of the theorem you wrote, not of the property you meant. A
true theorem about the wrong statement is the worse of the two failures: it is
cached, reported as verified, and read by a human as evidence about the function.
Nothing downstream can catch it, so catch it here — these are the questions to
put to your own theorem before it goes to the check endpoint.

Does every hypothesis earn its place? A precondition added because the proof
would not otherwise go through narrows the claim. If the theorem assumes
`(h : l ≠ [])` and the function handles the empty list, you proved less than the
property says. Either it belongs in the property's preconditions, where a reader
will see it, or it should not be in the signature.

Is it vacuous? Hypotheses that cannot all hold at once prove anything at all.
Name one concrete input that satisfies them; if you cannot, the theorem is empty.

Is it trivially true? If both sides reduce to the same expression and `rfl`
closes the goal, you restated the definition rather than a property of it. Real
identities do sometimes close on `rfl` — the question is whether the statement
would still be worth proving if the function were written differently.

Does it quantify what you meant? A free variable in the signature is universally
quantified, and one you fixed to a literal is a single example. Check the
direction of every implication and iff too: the converse is a different claim.

Does it still say what the spec file says? The `formal` and `description` fields
are what a human reads in the diff and what a cache hit reports back. If the
theorem drifted from them while you were proving it, the spec file is now wrong;
correct it there. `formal` is part of the cache key, so an honest correction
costs a re-proof, and that is the right price for the record being true.
