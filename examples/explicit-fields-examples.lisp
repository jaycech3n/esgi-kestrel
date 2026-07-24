; Runnable examples for the explicit finite-field development.
; From the repository root: (ld "examples/explicit-fields-examples.lisp")

(in-package "ACL2")
(ld "../hasse/explicit-fields-top.lisp")

; -----------------------------------------------------------------------------
; Prime fields
; -----------------------------------------------------------------------------

(defconst *example-f5* (ff-prime 5))

(assert-event (ff-field-p *example-f5*))
(assert-event (equal (ff-elements *example-f5*) '(0 1 2 3 4)))
(assert-event (equal (ff-add 4 3 *example-f5*) 2))
(assert-event (equal (ff-neg 2 *example-f5*) 3))
(assert-event (equal (ff-mul 3 4 *example-f5*) 2))
(assert-event (equal (ff-inv 2 *example-f5*) 3))
(assert-event (equal (ff-div 4 2 *example-f5*) 2))
(assert-event (equal (ff-frobenius 3 *example-f5*) 3))

; -----------------------------------------------------------------------------
; F_4 = F_2[T]/(T^2+T+1)
; -----------------------------------------------------------------------------

(defconst *example-f4* (ff-extension 2 '(1 1 1)))
(defconst *example-t* '(0 1))

(assert-event (ff-field-p *example-f4*))
(assert-event (equal (ff-cardinality *example-f4*) 4))
(assert-event (equal (len (ff-elements *example-f4*)) 4))
(assert-event (member-equal nil (ff-elements *example-f4*)))
(assert-event (member-equal '(1) (ff-elements *example-f4*)))
(assert-event (member-equal *example-t* (ff-elements *example-f4*)))
(assert-event (pf-polynomial-p *example-t* 2))
(assert-event (ff-element-p *example-t* *example-f4*))

; Addition stays in the canonical representative set without long division.
(assert-event
 (equal (ff-add *example-t* '(1 1) *example-f4*) '(1)))
(assert-event
 (ff-element-p (ff-add *example-t* '(1 1) *example-f4*) *example-f4*))

; T^2 = T+1 modulo T^2+T+1 in characteristic 2.
(assert-event
 (equal (ff-mul *example-t* *example-t* *example-f4*) '(1 1)))

; T(T+1)=1, so T+1 is the inverse of T.
(assert-event
 (equal (ff-inv *example-t* *example-f4*) '(1 1)))
(assert-event
 (equal (ff-mul *example-t*
                (ff-inv *example-t* *example-f4*)
                *example-f4*)
        '(1)))

; The field-cardinality Frobenius x |-> x^4 is the identity on F_4.
(assert-event
 (equal (ff-frobenius *example-t* *example-f4*) *example-t*))

; -----------------------------------------------------------------------------
; Polynomials over prime fields
; -----------------------------------------------------------------------------

; Coefficients are constant-first.  Normalization reduces modulo p and trims.
(assert-event
 (equal (pf-poly-normalize '(6 -1 0 0) 5) '(1 4)))

(assert-event
 (equal (pf-poly-add '(1 2) '(4 3 1) 5) '(0 0 1)))

(assert-event
 (equal (pf-poly-mul '(1 1) '(1 1) 5) '(1 2 1)))

(assert-event
 (equal (pf-poly-eval-horner '(1 2 1) 2 5) 4))

; X^2 reduces to X+1 in F_4.
(assert-event
 (equal (pf-poly-mod '(0 0 1) '(1 1 1) 2) '(1 1)))

; -----------------------------------------------------------------------------
; Irreducible-polynomial verification and construction
; -----------------------------------------------------------------------------

(assert-event
 (equal (find-irreducible-polynomial 2 4) '(1 0 0 1 1)))

(assert-event
 (pf-irreducible-by-trial-p
  (find-irreducible-polynomial 2 4) 2))

(defconst *example-f16* (construct-extension-field 2 4))

(assert-event (ff-general-field-p *example-f16*))
(assert-event (equal (ff-cardinality *example-f16*) 16))
(assert-event (equal (len (ff-elements *example-f16*)) 16))

; -----------------------------------------------------------------------------
; Checked quotient/remainder certificates
; -----------------------------------------------------------------------------

(defconst *example-divmod*
  (find-pf-divmod-certificate '(1 0 0 0 1) '(1 1 1) 2))

(assert-event
 (equal *example-divmod* '(:pf-divmod (0 1 1) (1 1))))

(assert-event
 (pf-divmod-certificate-p
  '(1 0 0 0 1) '(1 1 1) 2 *example-divmod*))

; -----------------------------------------------------------------------------
; Curves and finite point enumeration
; -----------------------------------------------------------------------------

(defconst *example-curve-f5* (ffc-curve 1 1))

(assert-event (ffc-curve-p *example-curve-f5* *example-f5*))
(assert-event
 (ffc-on-curve-p (ffc-point 0 1) *example-curve-f5* *example-f5*))
(assert-event
 (not (ffc-on-curve-p (ffc-point 0 0)
                      *example-curve-f5* *example-f5*)))
(assert-event
 (member-equal (ffc-infinity)
               (ffc-points *example-curve-f5* *example-f5*)))

; Frobenius on points over F_5 fixes every coordinate.
(assert-event
 (equal (ffc-frobenius-point (ffc-point 0 1) *example-f5*)
        (ffc-point 0 1)))

; -----------------------------------------------------------------------------
; A curve over the non-prime finite field F_25
; -----------------------------------------------------------------------------

; The constructor chooses X^2+X+1, irreducible over F_5.
(defconst *example-f25* (construct-extension-field 5 2))
(defconst *example-u-f25* '(0 1))

(assert-event
 (equal *example-f25* '(:extension 5 (1 1 1))))
(assert-event (ff-general-field-p *example-f25*))
(assert-event (equal (ff-cardinality *example-f25*) 25))
(assert-event (equal (len (ff-elements *example-f25*)) 25))

; y^2 = x^3+x+1.  Coefficients from F_5 are represented as constant
; polynomials in F_25.  Its discriminant is nonzero in characteristic 5.
(defconst *example-curve-f25* (ffc-curve '(1) '(1)))

(assert-event (ffc-curve-p *example-curve-f25* *example-f25*))
(assert-event
 (ffc-on-curve-p (ffc-point nil '(1))
                 *example-curve-f25* *example-f25*))
(assert-event
 (ffc-on-curve-p (ffc-point '(2 3) '(2))
                 *example-curve-f25* *example-f25*))

; Exhaustive enumeration finds 26 affine points plus infinity.
(assert-event
 (equal (ffc-point-count *example-curve-f25* *example-f25*) 27))

; The cardinality Frobenius z |-> z^25 fixes F_25 and therefore its points.
(assert-event
 (equal (ff-frobenius *example-u-f25* *example-f25*)
        *example-u-f25*))
(assert-event
 (equal (ffc-frobenius-point
         (ffc-point '(2 3) '(2)) *example-f25*)
        (ffc-point '(2 3) '(2))))

; -----------------------------------------------------------------------------
; Splitting certificates
; -----------------------------------------------------------------------------

; X^2+X has the two distinct roots 0 and 1 over F_2.
(defconst *example-splitting-certificate*
  (splitting-certificate *ff2* '(0 1)))

(assert-event
 (splitting-certificate-p
  '(0 1 1) *example-splitting-certificate*))

(assert-event
 (square-free-splitting-certificate-p
  '(0 1 1) *example-splitting-certificate*))

(assert-event
 (equal (len (splitting-certificate-roots
              *example-splitting-certificate*))
        2))
