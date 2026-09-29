# Hasse theorem ACL2 development

This directory contains an ACL2 development toward Hasse's theorem for
elliptic curves.  It currently has two layers:

1. an **executable finite-field layer**, which represents finite fields,
   polynomials, curves, and finite certificates concretely; and
2. an **abstract theorem layer**, which states the field, curve-group,
   polynomial-root, and endomorphism properties needed by the intended proof.

These layers are not yet connected.  In particular, the abstract layer should
not currently be described as a complete or loadable proof of Hasse's theorem.

## Current status

The status below was checked with ACL2 8.7 on 29 September 2026.

### Working now

- `explicit-fields-top.lisp` loads the concrete finite-field stack in dependency
  order.
- `../examples/explicit-fields-examples.lisp` completes with **54 passing
  `assert-event`s and no ACL2 errors**.
- Prime-field arithmetic, polynomial normalization/arithmetic, simple quotient
  extensions, finite-field element enumeration, exhaustive curve-point
  enumeration, the cardinality-power Frobenius, trial irreducibility search,
  quotient/remainder certificate search, and root-list certificate checking all
  run on the supplied examples.
- The examples cover `F_5`, `F_4`, a constructed `F_16`, a constructed `F_25`,
  a 27-point short Weierstrass curve over `F_25`, a polynomial division over
  `F_2`, and a two-root splitting certificate over `F_2`.
- Many local supporting theorems in the concrete files are admitted by ACL2,
  including normalization facts, addition closure, the soundness of the finite
  certificate search, and concrete `F_4`/`F_16` regression facts.

Run the checked examples from the `examples` directory:

```sh
cd examples
acl2 < explicit-fields-examples.lisp
```

ACL2 prints `:PASSED` for each successful assertion.  Its process can still
exit with status 0 after an ACL2 event failure, so also check the output for
`ACL2 Error` or `FAILED`.

### Not working or not complete

- `field.lisp` did not finish admitting its `encapsulate` in the tested run.
  After 140 seconds and about 29.6 million prover steps, ACL2 was interrupted
  at `FMUL-CLOSED`; the remaining checkpoint is the missing proof that
  polynomial reduction makes the product representative shorter than the
  modulus.  Consequently `elliptic-curve.lisp`,
  `frobenius.lisp`, `lemma-4-5.lisp`, `lemma-4-7.lisp`,
  `endomorphisms.lisp`, `rational_function.lisp`, and
  `proposition-2-21.lisp` cannot currently be loaded through their normal
  dependency chain.
- The concrete witnesses in `field.lisp` also need representation work.  The
  ambient field is represented as `F_25` polynomial lists, while `fq-elt-p`
  recognizes prime-field integers.  There is no embedding from those integers
  to constant polynomials.  In addition, `fsub` and `fdiv` are declared in the
  encapsulate signature but have no local witness definitions.
- `package.lsp` fails when loaded: `(*acl2-exports*)` is read as a function call.
  A package export-list constant would normally be supplied as
  `*acl2-exports*`, without the surrounding parentheses.  Nothing else in this
  directory currently uses the `HASSETHM` package.
- There is no concrete elliptic-curve addition or negation implementation.
  `ec-add`, `ec-neg`, and `ec-group-p` are constrained abstract functions.
- There is no executable rational endomorphism implementation.  The
  endomorphism functions and the ambient polynomial operations in
  `polynomials.lisp` are also constrained abstract functions.
- Proposition 2.21 is conditional on
  `endo-kernel-list-is-complete-p`; the fibre-to-kernel bijection has not been
  formalized.
- The square-free splitting-certificate checker verifies that every supplied
  value is a distinct root and that the root count equals the polynomial
  degree.  It does not construct a splitting field or reconstruct/factor the
  polynomial from the roots.
- The general irreducibility code is an executable reference checker.  The
  project has not yet proved that `pf-poly-mod` implements Euclidean division,
  that the trial predicate is equivalent to mathematical irreducibility, or
  that an irreducible polynomial is found for every prime and positive degree.
- `ff-inv` uses `x^(q-2)` and returns zero for zero; therefore `ff-div` also
  returns zero on a zero divisor.  Callers must exclude division by zero.
- The implemented extensions are only one level over `F_p`; recursive field
  towers and compatible embeddings are absent.
- The curve layer uses short Weierstrass equations without enforcing
  nonsingularity or excluding characteristics 2 and 3.

## Representations

Prime fields are descriptors of the form `(:prime p)`, with elements represented
by the integers `0` through `p-1`.

Simple extensions are descriptors of the form
`(:extension p modulus)`, denoting `F_p[T]/(modulus)`.  Extension elements and
all prime-field polynomials are coefficient lists in **constant-first order**.
For example, `(1 0 1)` means `1 + T^2`.  The empty list `nil` is the zero
polynomial and trailing zero coefficients are removed.

There are two field predicates:

- `ff-field-p` in `finite-fields.lisp` uses the older root-based
  irreducibility check and accepts extension degrees only 1, 2, and 3.
- `ff-general-field-p` in `irreducible-polynomials.lisp` uses exhaustive trial
  division and accepts descriptors such as the constructed degree-four
  `*ff16*`.

The arithmetic functions operate from a descriptor and do not themselves call
either predicate.  Code that needs a verified descriptor must choose the
appropriate predicate explicitly.  In particular, `splitting-certificate-p`
currently requires the narrower `ff-field-p`.

Abstract elliptic-curve points use either `:infinity` or
`(:affine x y)`.  The concrete curve layer uses the same point shapes and a
curve descriptor `(:short-weierstrass a b)`.

## File and function reference

### `finite-fields.lisp`

This is the main executable arithmetic implementation.

Prime-field utilities:

- `pf-normalize` reduces an integer modulo `p`, using defensive defaults for
  malformed inputs.
- `pf-element-p` recognizes canonical integers in `F_p`.
- `no-divisor-at-or-below-p` performs the recursive factor search used by
  `prime-number-p`.
- `prime-number-p` tests primality by trial division through `floor(p/2)`.

Dense polynomial utilities over `F_p`:

- `pf-poly-trim` removes trailing zero coefficients.
- `pf-poly-coefficients-p` checks that every coefficient is canonical in
  `F_p`; `pf-polynomial-p` additionally requires a true, already-trimmed list.
- `pf-poly-normalize` reduces every coefficient modulo `p` and trims the
  result; `pf-poly-degree` returns `length - 1`, with degree 0 assigned to the
  zero polynomial.
- `pf-poly-add`, `pf-poly-neg`, `pf-poly-sub`, `pf-poly-scale`, and
  `pf-poly-mul` implement the usual dense polynomial operations modulo `p`.
- `pf-poly-leading-coefficient` obtains the normalized leading coefficient.
- `zeros` and `pf-poly-butlast` are helpers for shifted polynomial reduction.
- `pf-poly-reduce-once` cancels one leading term against a **monic** modulus.
  Its result is not valid for a non-monic modulus.
- `pf-poly-mod-aux` repeatedly reduces while fuel remains;
  `pf-poly-mod` normalizes the inputs and supplies the original dividend length
  as fuel.
- `pf-poly-eval-horner` evaluates a polynomial by Horner's rule.
- `pf-poly-has-no-root-below-p` checks all base-field values below a bound.
- `pf-irreducible-p` is the older checker: it accepts monic degree-one
  polynomials and monic degree-two or degree-three polynomials with no root in
  `F_p`.

Finite-field descriptors and arithmetic:

- `ff-prime` and `ff-extension` construct descriptors; `ff-kind`,
  `ff-characteristic`, and `ff-modulus` are accessors.
- `ff-field-p` validates a prime descriptor or a simple extension accepted by
  `pf-irreducible-p`.
- `ff-degree` and `ff-cardinality` return the extension degree and `p^degree`.
- `ff-normalize` reduces a prime element modulo `p` or an extension element
  modulo the defining polynomial.
- `ff-element-p` recognizes canonical field representatives.
- `ff-zero`, `ff-one`, `ff-add`, `ff-neg`, and `ff-mul` implement basic field
  operations.  `ff-add-closed` is proved; the corresponding general
  multiplication-closure theorem is still missing.
- `ff-pow` uses straightforward recursive exponentiation.
- `ff-inv` uses finite-field exponentiation by `q-2`; `ff-div` multiplies by
  that result.
- `naturals-below`, `prepend-each`, `prepend-all`, and `coefficient-vectors`
  construct coefficient vectors used for exhaustive enumeration.
- `ff-normalize-list` normalizes a list of candidate elements.
- `ff-elements` enumerates every canonical representative in the described
  prime field or simple extension.
- `ff-frobenius` computes `x^q`, where `q` is the descriptor's cardinality.
  On elements of that same finite field this is the identity map; it is not yet
  the nontrivial `q`-power map on a larger ambient extension.

`*ff2*` and `*ff4*` are concrete regression constants.  The final block after
them is inside an ACL2 `#| ... |#` comment and consists of unfinished proof
experiments; it is not loaded.

### `euclidean-division.lisp`

This file expects `finite-fields.lisp` to have already been loaded.

- `pf-poly-equal` compares normalized polynomial representatives.
- `pf-division-monic-polynomial-p` recognizes a nonzero normalized monic
  divisor.
- `pf-remainder-degree-bounded-p` checks that a remainder is zero or shorter
  than its divisor.
- `pf-divmod-certificate` constructs
  `(:pf-divmod quotient remainder)`; `pf-divmod-quotient` and
  `pf-divmod-remainder` extract its fields.
- `pf-divmod-certificate-p` checks primality, a monic divisor, the reconstruction
  `dividend = quotient*divisor + remainder`, and the remainder degree bound.
- `normalize-polynomial-list` and `polynomials-of-length-at-most` generate the
  normalized candidates used by exhaustive search.
- `find-remainder-for-quotient` and `find-pf-divmod-certificate-aux` are the
  first version of the nested candidate search.
- `divmod-certificates-for-quotient`, `all-divmod-certificates`, and
  `find-valid-divmod-certificate` build and scan an explicit certificate list;
  this is the path used by the public search function.
- `find-pf-divmod-certificate` sets degree-derived search bounds and returns the
  first valid certificate, or `nil` for an invalid input or unsuccessful
  search.

ACL2 proves that a non-`nil` result selected by
`find-valid-divmod-certificate` is valid.  It does not yet prove that
`find-pf-divmod-certificate` succeeds for every valid dividend and divisor.
`*pf-divmod-example*` is the checked `F_2` regression example.

### `irreducible-polynomials.lisp`

This file also expects `finite-fields.lisp` first.

- `append-monic-leading-one` turns coefficient vectors into monic
  polynomials.
- `monic-polynomials-of-degree` and `monic-polynomials-through-degree`
  exhaustively enumerate monic candidates.
- `pf-zero-polynomial-p`, `pf-poly-divides-p`, and
  `some-polynomial-divides-p` implement normalized-zero and trial-divisibility
  tests using `pf-poly-mod`.
- `pf-monic-polynomial-p` recognizes a normalized monic polynomial.
- `pf-irreducible-by-trial-p` accepts a positive-degree monic polynomial when
  no monic polynomial through half its degree divides it.
- `find-first-irreducible` scans candidates;
  `find-irreducible-polynomial` generates degree-`n` candidates and returns the
  first accepted one.
- `ff-general-field-p` validates prime fields and extensions using the general
  trial predicate.
- `construct-extension-field` searches for a modulus and constructs an
  extension descriptor, returning `nil` if the search does not produce one.

The search-result theorems establish soundness relative to the executable
trial predicate, not yet to a separately formalized mathematical definition of
irreducibility.  `*ff16-modulus*` and `*ff16*` are degree-four regression
constants.

### `finite-field-curves.lisp`

This is the executable curve layer.

- `ffc-curve` constructs `(:short-weierstrass a b)`; `ffc-a` and `ffc-b` are
  accessors.
- `ffc-infinity` returns the point at infinity.
- `ffc-point` constructs `(:affine x y)`; `ffc-x` and `ffc-y` are accessors.
- `ffc-square` and `ffc-cube` use field multiplication.
- `ffc-curve-p` checks the descriptor shape and that `a` and `b` are elements
  of the supplied field.  It does not test the field descriptor or the curve
  discriminant.
- `ffc-on-curve-p` accepts infinity or checks
  `y^2 = x^3 + ax + b` for a well-shaped affine point.
- `ffc-points-with-x` filters a list of `y` values for one `x`;
  `ffc-affine-points` repeats this for all `x` values.
- `ffc-points` enumerates all affine points using `ff-elements` and prepends
  infinity; `ffc-point-count` returns the resulting length.
- `ffc-frobenius-point` applies `ff-frobenius` to both affine coordinates and
  fixes infinity.

Only the unconditional fact that infinity lies on the equation is presently
proved in this file.  No group law is defined here.

### `splitting-extensions.lisp`

- `sf-poly-eval-aux` evaluates a constant-first polynomial while carrying the
  current power of `x`; `sf-poly-eval` starts with field one.
- `all-ff-elements-p` checks that a list consists of elements of a field.
- `all-roots-p` checks that every listed value evaluates to field zero.
- `splitting-certificate` constructs
  `(:splitting-certificate field roots)`;
  `splitting-certificate-field` and `splitting-certificate-roots` are
  accessors.
- `splitting-certificate-p` checks the tag and shape, `ff-field-p`, root-list
  shape and membership, and that every supplied value is a root.
- `square-free-splitting-certificate-p` additionally requires distinct roots
  and exactly `pf-poly-degree(poly)` roots.

The theorem `square-free-certificate-root-count` merely exposes the final
length condition already present in the predicate; it does not prove that a
certificate exists or independently prove square-freeness.

### `explicit-fields-top.lisp`

Convenience loader for the five concrete files, in order:

1. `finite-fields.lisp`
2. `euclidean-division.lisp`
3. `irreducible-polynomials.lisp`
4. `finite-field-curves.lisp`
5. `splitting-extensions.lisp`

It does not load the abstract field/endomorphism development.

### `field.lisp`

Intended abstract interface for an ambient algebraic closure, a finite fixed
field, and Frobenius.  The encapsulate declares:

- `fe-p` and `fq-elt-p`, intended to recognize ambient and `F_q` elements;
- `fzero`, `fone`, `fadd`, `fmul`, `fsub`, and `fdiv`, intended as field
  constants and operations; and
- `frob`, intended as Frobenius.

It then attempts to constrain closure, Frobenius homomorphism laws, and the
equivalence between Frobenius-fixed ambient elements and `F_q` elements.
`fsquare` and `fcube` are simple wrappers around `fmul`.

This file is currently the first failing point in the abstract load chain; see
the status section above.

### `elliptic-curve.lisp`

Abstract short Weierstrass curves over the interface in `field.lisp`.

- `ec-infinity-p`, `ec-affine-point`, and `ec-affine-point-p` recognize or
  construct the two point forms.
- `ec-x` and `ec-y` extract affine coordinates; callers should first establish
  that the point is affine.
- `ec-point-p` accepts infinity or a well-formed affine point.
- `curve-rhs` computes `x^3 + ax + b` using the abstract operations.
- `on-curve-p` tests the curve equation, with infinity always on the curve.
- `fq-rational-point-p` additionally requires affine coordinates in `F_q`.
- `ec-add`, `ec-neg`, and `ec-group-p` are constrained, non-executable
  operations.  Their closure, identity, associativity, and inverse laws are
  assumed within an encapsulate when `ec-group-p` holds.
- `ec-translate-list` adds a fixed offset to every point in a list.

`ec-subtract-equal-iff` derives group cancellation from the abstract group
laws, and `len-of-ec-translate-list` proves that list translation preserves
length.  The local witness makes `ec-group-p` false, so the encapsulate does not
construct a concrete curve group.

### `frobenius.lisp`

- `frobenius-point` fixes infinity and applies abstract `frob` to both affine
  coordinates.

The file also proves, assuming the `field.lisp` interface, that Frobenius
commutes with squaring, cubing, and the curve right-hand side.

### `lemma-4-5.lisp`

Contains no new executable functions.  It is intended to prove Washington's
Lemma 4.5: Frobenius preserves a curve defined over `F_q`, and the fixed curve
points are exactly the `F_q`-rational points.  These theorem events are
currently unreachable because `field.lisp` does not load.

### `lemma-4-7.lisp`

- `frob-minus-one` computes the abstract group expression
  `Frobenius(P) + (-P)`.

`ker-frob-sub-one` is intended to identify its kernel with the `F_q`-rational
points, conditional on the abstract group and field assumptions.  It depends
on `lemma-4-5.lisp` and is not currently loadable.

### `polynomials.lisp`

Abstract polynomials over the intended ambient field.

- `field-polynomial-p` checks that every coefficient satisfies `fe-p`.
- `polynomial-degree` returns `length - 1`, assigning degree 0 to the empty
  list.
- `poly-eval`, `poly-sub`, `poly-scale`, `poly-derivative`,
  `square-free-polynomial-p`, `splits-polynomial-p`, and
  `polynomial-root-list` are constrained, non-executable operations.

The encapsulated theorems specify that a square-free split polynomial has a
duplicate-free root list, characterize list membership, and give the expected
root count.  The local witnesses make the square-free and split predicates
false, so this is an interface boundary rather than a construction of roots.

### `endomorphisms.lisp`

Abstract rational endomorphisms and the intended Washington Proposition 2.21
argument.

The following are constrained and non-executable:

- `endomorphism-p`, `nonzero-endomorphism-p`, and
  `separable-endomorphism-p` recognize the intended hypotheses;
- `endo-apply` applies an endomorphism;
- `endo-numerator`, `endo-denominator`, and `endo-y-factor` expose its rational
  representation;
- `endo-degree` gives its degree; and
- `endo-good-target`, `endo-good-preimage`, and
  `endo-good-fiber-list` stand for the specially chosen fibre in Washington's
  proof.

The encapsulate assumes curve mapping, addition preservation, preservation of
infinity, the good-fibre length, and the chosen preimage property.

The executable wrappers built on that interface are:

- `endo-kernel-point-p`, which tests whether an on-curve point maps to
  infinity;
- `endo-kernel-list`, which translates the good fibre by the inverse of a
  chosen preimage; and
- `endo-kernel-cardinality`, which is the length of that list.

`endo-kernel-list-is-complete-p` is a quantified condition saying this list is
exactly the kernel.  `proposition-2-21-separable` proves degree equals that list
length only when this condition and the other abstract hypotheses are
supplied.  The local recognizer witnesses are false, so the encapsulate does
not supply a concrete endomorphism.

### Loader and package files

- `proposition-2-21.lisp` is only a named loader for `endomorphisms.lisp`.
- `rational_function.lisp` is a compatibility loader for `field.lisp` and
  `polynomials.lisp`; new code should load `polynomials.lisp` directly once the
  abstract dependency is repaired.
- `package.lsp` attempts to define `HASSETHM`, but currently fails as described
  above.  All substantive files presently use the `ACL2` package.

## Suggested next proof steps

The nearest blocking tasks are:

1. prove a strict output-length/remainder bound for `pf-poly-mod` and use it to
   prove multiplication closure for accepted extension-field representatives;
2. give `field.lisp` consistent local witnesses, including an explicit
   embedding of base-field elements into the ambient extension and witnesses
   for `fsub` and `fdiv`;
3. re-run the abstract loaders and repair any proof obligations exposed after
   `FMUL-CLOSED`;
4. prove the Euclidean-division specification for `pf-poly-mod`, then connect
   the trial checker to mathematical irreducibility; and
5. implement the concrete elliptic-curve group law and discharge the
   endomorphism fibre-completeness condition.

The repository-level `DESIGN.md` contains additional mathematical motivation,
but its status paragraph predates the current `field.lisp` failure.  This file
records the behavior observed from the current sources.
