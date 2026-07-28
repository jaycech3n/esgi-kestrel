# Executable examples

These examples exercise the public functions in the explicit finite-field
development. Keep this directory synchronized with new public functions and
representation changes.

Run ACL2 from the repository root:

```sh
acl2
```

Then, at the ACL2 prompt:

```lisp
(ld "examples/explicit-fields-examples.lisp")
```

The file uses `assert-event`, so a changed implementation or unexpected result
causes the load to fail.

## Representation conventions

Polynomials are coefficient lists in ascending degree order:

```text
(a0 a1 a2)  represents  a0 + a1*X + a2*X^2.
```

The empty list is the zero polynomial. Extension-field elements use the same
representation, reduced modulo the field's defining polynomial.

Points use:

```lisp
:infinity
(:affine x y)
```

## Covered examples

- arithmetic in `F_5`;
- construction and enumeration of `F_4`;
- canonical extension-field representatives and closure of addition in `F_4`;
- multiplication, inversion, and Frobenius in `F_4`;
- polynomial normalization, arithmetic, evaluation, and reduction;
- explicit leading-term cancellation in one polynomial-reduction step;
- arbitrary-degree irreducibility search and construction of `F_16`;
- checked quotient/remainder certificates;
- short Weierstrass curve point enumeration over `F_5`;
- construction of `F_25` and a 27-point curve over that non-prime field;
- finite splitting certificates.
