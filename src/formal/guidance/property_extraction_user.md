For each pure function you identified, work out the properties worth proving about it,
and assess each one for Lean formalizability in the same pass.

A property is VERIFIABLE if:
- It can be expressed purely in terms of mathematical structures
  (numbers, lists, sets, booleans, strings with structural equality)
- Every type involved can be mapped to a concrete Lean 4 type:
    equality / comparison  →  = or ≤ on the relevant type
    membership             →  ∈ Finset / ∈ List
    optional / nullable    →  Option T
    text / string          →  List Char (NOT String — see the modeling note below)
    ordered collection     →  List T or Finset T
    map / dictionary       →  Finset (K × V) or a function K → Option V
- The proof does not require axioms about runtime behaviour
  (memory layout, allocator or GC behaviour, hash codes, pointer or reference identity,
  iteration order of an unordered collection, etc.)

Modeling assumptions applied during verification:
- Floating-point types are modeled as Rat (rationals) — NaN, Inf, IEEE 754 rounding do not exist.
- Strings are modeled as List Char, not Lean's String. String equality is structural.
- Collections are modeled as Finset or List with standard membership.

A property is UNVERIFIABLE only if it fundamentally depends on something outside these models:
- Reference/pointer identity (not value equality)
- Runtime type information or reflection
- Hash codes or memory addresses
- External state, I/O, or time

String properties — verifiability rules:
- `startsWith` / `isPrefixOf` with free-variable strings: verifiable.
  Add to assumptions: "Strings modeled as List Char; proof via simp [List.isPrefixOf]"
- String injectivity WITHOUT a separator precondition (e.g. f(a,b) = prefix++a++mid++b is injective
  because prefix and mid are unique delimiters): verifiable.
  Add to assumptions: "Strings modeled as List Char; proof via List.append_inj"
- String injectivity WITH a separator precondition (the proof requires assuming the separator does
  NOT appear inside either input string): not verifiable. Substring-absence reasoning is not
  something Lean and Mathlib discharge within practical timeouts — it always times out.

When in doubt, treat it as verifiable — ordering, bounds, identity, idempotency, and
monotonicity properties are almost always verifiable under these models.

Write the ones you judge verifiable into the spec file described by GET /guide, and drop
the rest — there is no field for an unverifiable property, and nothing downstream reads
one. If leaving something out was a real decision, say so in your report to the user;
the spec file records what you are checking, not what you considered.

%%KINDS%%

Pick the one that describes the shape of the statement. `kind` is part of the cache key,
so use the same one for the same property across runs; when two fit, prefer the more
specific. The id is not in the key — renaming a property keeps its cached proof and only
changes the diff a human reads.

Aim for 2-5 properties per pure function. There is no total cap: a file with six pure
functions warrants more than a file with one. Prefer a few properties that would catch a
real mistake over many that restate the implementation, and prefer proving one strong
property to stating three weak ones.

Model a sequence as `List Char` when the source treats it as text — comparing, matching,
concatenating, indexing to get a character. Model it as `List Nat` (or `List UInt8`) when
the source treats the elements as numbers: arithmetic on them, range comparisons, bit
operations. What decides it is what the code does with an element, not what the language
calls the type.

The `List Char` rule exists because Lean's `String` is unusable in proofs, not because
every sequence is text. Forcing `Char` onto element arithmetic drags validity side
conditions into a proof that has none. When you model elements as numbers, record the
range you are assuming — the model does not enforce it.

