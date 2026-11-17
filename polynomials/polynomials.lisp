;;; Univariate polynomials over prime fields ℤₚ := ℤ/pℤ.

(ld "../prelude.lisp")
(ld "../prime-fields.lisp")

; We represent a polynomial cs ∈ ℤₚ[x] by a "little endian" list of
; coefficients, where the entry cₖ at index k is the coefficient of xᵏ.

; Remark:
; An alternative (see e.g. Medina et al's polynomials book or Lean's mathlib)
; is to represent cs as an ordered list of (degree, coefficient) pairs (k, cₖ),
; ordered by k, with no cₖ zero.
; This will likely make certain proofs easier, but I am unsure about the
; efficiency/proof ease tradeoff.

; Definition disabled for better abstraction in proofs.
(define polyp (cs p)
  :guard (posp p)
  (pfield::all-fep cs p))

(defun constpolyp (cs p)
  (and (polyp cs p) (singletonp cs)))

; Locally reenable `polyp` to implement
; basic operations and properties.
(section
(local (in-theory (enable polyp)))

;; ==== Operations ====

; Recognizes *any* list of zeroes.
(defun zeropolyp (cs p)
  (and (polyp cs p) (all-equalp 0 cs)))

(defun nonzeropolyp (cs p)
  (and (polyp cs p) (not (all-equalp 0 cs))))

; Normalizes a polynomial representation by removing trailing zeros.
(defun poly-nf (cs)
  (dropvals-from-end 0 cs))

; We say the degree of the zero polynomial is -1 (instead of -∞).
(defun poly-deg (cs)
  (let ((nf (poly-nf cs)))
    (if (nilp nf) -1 (1- (len nf)))))

(define poly-scale (c cs p)
  :enabled t
  :guard (and (posp p)
              (pfield::fep c p)
              (polyp cs p))
  (pfield::mapmul c cs p))

; Let us call multiplying cs ∈ ℤₚ[x] by (powers of) x, "shifting" cs.
(define poly-shift (n cs)
  :enabled t
  :guard (natp n)
  (if (zp n) cs (cons 0 (poly-shift (1- n) cs))))

; Quick function to define monomials of degree n and coefficient c.
(define monomial (n c)
  :enabled t
  :guard (natp n)
  (poly-shift n (list c)))

; Doesn't trim trailing zeros
(define poly+ (as bs p)
  :guard (and (posp p)
              (polyp as p)
              (polyp bs p))
  (if (and (polyp as p) (polyp bs p))
      (cond ((atom as) bs)
            ((atom bs) as)
            ((and (consp as) (consp bs))
              (cons (pfield::add (first as) (first bs) p)
                    (poly+ (rest as) (rest bs) p))))
      :[poly+]-bad-inputs))

; Need the following to prove the guard condition for poly*.
(defrule all-fep-poly+
  (implies (and (posp p)
                (pfield::all-fep as p)
                (pfield::all-fep bs p))
           (pfield::all-fep (poly+ as bs p) p))
  :enable poly+)

(define poly*-ind (as bs)
  :enabled t
  :measure (+ (len as) (len bs))
  (cond ((and (consp as) (consp bs))
         (and (poly*-ind (rest as) (rest bs))
              (poly*-ind (rest as) bs)
              (poly*-ind as (rest bs))))
        (t t)))

(define poly* (as bs p)
  :enabled t
  :guard (and (posp p)
              (polyp as p)
              (polyp bs p))
  :guard-hints (("Goal" :induct (poly*-ind as bs)))
  (if (and (polyp as p) (polyp bs p))
      (cond ((or (atom as) (atom bs)) nil)
            ((and (consp as) (consp bs))
              (poly+ (poly-scale (first as) bs p)
                     (poly-shift 1 (poly* (rest as) bs p))
                     p)))
      :[poly*]-bad-inputs))

(define poly-neg (cs p)
  :enabled t
  :guard (and (posp p) (polyp cs p))
  (pfield::mapneg cs p))

(define poly- (as bs p)
  :enabled t
  :guard (and (posp p)
              (polyp as p)
              (polyp bs p))
  (poly+ as (poly-neg bs p) p))

)