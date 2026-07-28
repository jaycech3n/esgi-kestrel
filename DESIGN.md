# Hasse theorem ACL2 development: design and mathematics

This is a living document.  Update it whenever a representation, assumption,
proof boundary, or dependency changes.

Runnable usage examples live in `examples/`. New public executable functions
and representation changes should update
`examples/explicit-fields-examples.lisp` and its README in the same change.

## Goal and current strategy

The eventual goal is a mechanically checked proof of Hasse's theorem following
Washington's *Elliptic Curves: Number Theory and Cryptography*.  The current
Chapter 4 path proves the fixed-point part of Proposition 4.7 abstractly.  The
new explicit-field path supplies finite witnesses for fields, extensions,
points, fibres, and kernels.

We do **not** represent the algebraic closure as a completed infinite ACL2 set.
Every finite collection of algebraic elements lies in a finite extension, so
proofs instead carry a sufficiently large finite extension (or a certificate
that a polynomial splits in it).  This keeps witnesses finite and executable.

## Logical layers

1. `hasse/field.lisp` is the old abstract interface used by the already proved
   Lemma 4.5 and Proposition 4.7 work.
2. `hasse/finite-fields.lisp` is the new executable representation.  It is kept
   separate until all abstract operations can be instantiated without breaking
   existing proofs.
3. `hasse/finite-field-curves.lisp` defines curves, enumerates their points,
   and defines Frobenius using explicit field descriptors.
4. `hasse/splitting-extensions.lisp` specifies finite certificates replacing
   appeals to the algebraic closure.
5. `hasse/endomorphisms.lisp` contains the abstract rational-endomorphism and
   Washington Proposition 2.21 interfaces.

## Explicit fields

A prime field is represented by `(:prime p)`.  Its elements are the canonical
integers `0,...,p-1`.

A simple extension is represented by

```lisp
(:extension p modulus)
```

and denotes `F_p[T]/(modulus)`.  An element is a trimmed coefficient list in
ascending order, of degree less than `degree(modulus)`.  Addition is
coefficientwise modulo `p`; multiplication is polynomial multiplication followed
by reduction modulo the monic modulus.

`pf-polynomial-p` makes the canonical-representative invariant explicit: the
object is a true list, every coefficient is a canonical element of `F_p`, and
there are no trailing zero coefficients.  `ff-element-p` additionally requires
an extension-field representative to be shorter than the normalized modulus.
This direct invariant replaced the earlier indirect test
`x = ff-normalize(x)`, which made even addition closure depend on proving the
full idempotence specification of polynomial long division.

For a monic modulus, `pf-poly-reduce-once` constructs the result after the two
equal leading terms have cancelled: it removes the leading coefficient from
both the dividend and modulus and subtracts the appropriately shifted, scaled
tails.  This is extensionally the usual subtraction by a shifted multiple of a
monic modulus, but exposes the strict length decrease directly to ACL2.
`len-of-pf-poly-reduce-once-decreases` is proved by bounding the two remaining
summands below the original dividend length.

ACL2 now proves `ff-add-closed` for every descriptor accepted by `ff-field-p`.
For prime fields this follows from the standard bounds on `mod`.  For extension
fields, coefficientwise addition preserves canonical coefficients and cannot
increase the maximum input length.  Consequently, two representatives of
degree below the modulus remain below it; polynomial division is neither
mathematically necessary nor executed by `ff-add`.

`ff-field-p` requires the modulus to be monic and to pass
`pf-irreducible-p`.  The current executable checker handles degrees 1, 2, and
3; in degrees 2 and 3, absence of a base-field root is equivalent to
irreducibility.  Higher degrees are currently rejected.  A later book should
add a verified general irreducibility test or certificate checker.

The current executable extension is one level over `F_p`.  General towers
`F_q[T]/h` need recursive field descriptors and compatible embeddings; this is
the next field-layer milestone.

The constants `*ff2*` and `*ff4*` are non-vacuous checked witnesses.  ACL2
proves that `*ff4* = F_2[T]/(T^2+T+1)` is accepted as a field and that its
canonical enumeration has four elements.

## Frobenius and rational points

For a finite field `F` of cardinality `q`, Frobenius is executable as

```lisp
(ff-pow x q F)
```

On `F` itself this is the identity.  On a future extension `L/F_q`, the relevant
map is also `x |-> x^q`, but the descriptor must retain the base field and its
embedding into `L`.

Curves use short Weierstrass form `y^2=x^3+Ax+B`.  The explicit layer takes a
field argument everywhere and can enumerate all points because `ff-elements`
is finite.  Characteristic 2 and 3 require either general Weierstrass equations
or explicit restrictions; the present short-form interface is intended for
characteristic different from 2 and 3.

## Algebraic closure via splitting certificates

A splitting certificate contains a finite extension and a list of roots.  Its
checker verifies that every listed element is a root, that the list has no
duplicates when square-freeness is claimed, and eventually that the factored
polynomial reconstructed from those roots equals the original polynomial.
Thus a theorem that says "a polynomial has roots over the algebraic closure"
will be stated as existence of a checked finite splitting certificate.

## Washington Proposition 2.21

For a nonzero endomorphism

`alpha(x,y) = (p(x)/q(x), y r2(x))`,

separability says `p' q - p q'` is not the zero polynomial.  Washington chooses
a target `(a,b)` so that `p-aq` has degree `deg(alpha)` and has no repeated
roots.  A splitting certificate for `p-aq` supplies exactly `deg(alpha)`
distinct roots.  Since `b` is nonzero, each root determines a unique point in
the fibre.  Translation by the inverse of one chosen preimage bijects that
fibre with the kernel.

`endo-kernel-list-is-complete-p` remains an explicit obligation until this
translation bijection is fully formalized.  A list length is not called a
kernel cardinality without this semantic completeness condition.

## Link to Proposition 4.7

For `d = Frobenius_q - 1`, Proposition 4.7(1) proves pointwise

`d(P)=infinity  <=>  P is F_q-rational`.

After proving that `d` is a nonzero separable endomorphism, Proposition 2.21
gives `deg(d)=#Ker(d)`.  Extensional equality of the duplicate-free kernel list
and the executable list of `F_q`-points then gives

`deg(Frobenius_q-1) = #E(F_q)`.

## Status

- Abstract Lemma 4.5 and the kernel characterization load successfully.
- Abstract group cancellation is derived from the group axioms.
- Prime fields and simple polynomial quotient extensions are executable.
- Explicit curve-point enumeration and Frobenius are executable.
- Irreducibility, splitting-certificate completeness, compatible extension
  towers, the concrete elliptic-curve group law, and the full Proposition 2.21
  fibre bijection remain proof obligations.

## Survey of installed ACL2 polynomial support

The installed ACL2 8.7 books were searched for finite extensions, Galois
fields, irreducible polynomials, polynomial factorization, and splitting
fields.  There is no ready-made construction of `F_(p^n)` and no theorem or
algorithm producing an irreducible polynomial of every prescribed degree over
`F_p`.

The closest reusable material is:

- `workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp`, which uses
  Kestrel prime-field operations and proves results about evaluation, roots,
  products, and numbers of roots;
- `nonstd/polynomials/`, which supplies general polynomial representations and
  algebraic lemmas;
- `workshops/2006/cowles-gamboa-euclid/`, which develops abstract Euclidean
  domains and irreducible factorization.  Its occurrences of "irreducible" are
  not a constructor for prescribed-degree polynomials over finite fields.

The first general checker is now implemented in
`hasse/irreducible-polynomials.lisp`.  It uses exhaustive trial division: a
monic polynomial of degree `n` is accepted when no monic polynomial of degree
between `1` and `floor(n/2)` divides it.  Divisibility is checked by the
polynomial remainder operation.  This is deliberately slower than Rabin's
criterion, but is a small, transparent reference implementation against which
a faster checker can later be validated.

`find-irreducible-polynomial` enumerates all monic degree-`n` polynomials and
returns the first accepted candidate.  ACL2 proves the soundness implication

```lisp
(implies (find-irreducible-polynomial p n)
         (pf-irreducible-by-trial-p
          (find-irreducible-polynomial p n) p)).
```

Here "soundness" currently means soundness with respect to the executable
predicate `pf-irreducible-by-trial-p`.  Before using it as the mathematical
irreducibility theorem, we must prove the Euclidean-division specification for
`pf-poly-mod` and then prove that the absence of monic divisors through degree
`floor(n/2)` is equivalent to the usual factorization definition of
irreducibility.  This semantic bridge is a prerequisite for the general
existence proof; it must not be replaced by an axiom.

Similarly, `construct-extension-field` turns a returned modulus into an
extension descriptor, and ACL2 proves that its modulus passes the checker.
`*ff16*` is a regression witness: the constructor finds
`X^4 + X^3 + 1` over `F_2`, and ACL2 proves that the resulting field descriptor
has a sixteen-element enumeration.

The faster planned checker is the finite-field/Rabin criterion.  For a monic
polynomial `f` of degree `n`, it checks

1. `X^(p^n) - X = 0 (mod f)`, and
2. `gcd(f, X^(p^(n/r)) - X) = 1` for every prime divisor `r` of `n`.

This requires polynomial gcd, modular
polynomial exponentiation, and enumeration of the prime divisors of `n`.
It should eventually be proved equivalent to the exhaustive reference checker.

Construction and verification remain logically separate.  The current bounded
search is sound if it returns a value.  To prove that it always succeeds, we
additionally need the
existence theorem that `F_p[X]` contains an irreducible polynomial of every
positive degree.  That existence proof is a later, substantive counting
argument (normally obtained from the factorization of `X^(p^n)-X` and the
formula for the number of monic irreducibles).  Until it is proved, callers may
supply an irreducibility certificate checked by the verified criterion, and the
exhaustive constructor works on concrete inputs, but we do not yet claim the
general non-nil theorem for every prime `p` and positive `n`.

### Dependency chain for the general existence theorem

The theorem

```lisp
(implies (and (prime-number-p p) (posp n))
         (find-irreducible-polynomial p n))
```

requires the following proved layers, in order:

1. Euclidean division over `F_p[X]`: `a = q*b+r` and `deg(r)<deg(b)` for
   nonzero monic `b`, together with correctness of `pf-poly-mod`.
2. Correctness of `pf-poly-divides-p` and equivalence of the trial predicate
   with mathematical irreducibility.
3. Formal derivative and square-free factorization of `X^(p^n)-X`; its roots
   are exactly the elements of fields whose degrees divide `n`.
4. The counting identity `p^n = sum_(d|n) d*N_p(d)`, where `N_p(d)` is the
   number of monic irreducibles of degree `d`.
5. Möbius inversion (or an equivalent induction) and positivity of `N_p(n)`.
6. Completeness of the finite enumeration used by
   `find-irreducible-polynomial`, yielding the non-nil constructor theorem.

## Proof-carrying Euclidean division

`hasse/euclidean-division.lisp` now defines a division certificate

```lisp
(:pf-divmod quotient remainder)
```

and `pf-divmod-certificate-p` checks, over `F_p[X]`, both

```text
dividend = quotient * divisor + remainder
```

and that the remainder is zero or has strictly smaller degree than the monic
divisor.  Equality is equality of normalized coefficient lists.

`find-pf-divmod-certificate` performs a finite exhaustive search over all
quotients and remainders within the Euclidean degree bounds.  The generic
search theorem `find-valid-divmod-certificate-is-valid` proves that every
non-nil result selected from a candidate list satisfies the certificate
predicate.  A concrete regression divides `X^4+1` by `X^2+X+1` over `F_2` and
checks the returned quotient `X^2+X` and remainder `X+1`.

The remaining division obligation is totality: prove that
`find-pf-divmod-certificate` is non-nil for every dividend and every nonzero
monic divisor.  The certificate checker and finite search are verified, but
this general existence theorem still requires a constructive long-division
proof.  Consequently the semantic bridge for `pf-poly-mod` is not yet marked
complete.

### Comparison with `barriecooper/acl2-schoof`

The sibling checkout and the linked GitHub repository were inspected.  Its
`docs/polynomial-library-audit.md` identifies the 2006
`workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/` chain as the only
installed ACL2 development with a certified general long-division theorem,
including quotient/remainder reconstruction and the strict remainder-degree
bound.  That library uses sparse polynomials over an abstract encapsulated
field and custom equality/normalization packages.  It does not directly
instantiate the dense, constant-first, explicit-`p` representation used here.

The Schoof repository records the same dense-polynomial division theorem as an
open obligation in `docs/obligations.md`; it contains architectural analysis,
not a completed dense PFIELD proof to import.  Reusing the old theorem would
therefore require a substantial representation isomorphism and functional
instantiation.  For this project the shorter route remains a direct invariant
proof for `pf-poly-reduce-once`/a quotient-accumulating long-division loop.
