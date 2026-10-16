;;; Univariate polynomials over prime fields ℤₚ := ℤ/pℤ.

(ld "prelude.lisp")
(ld "prime-fields.lisp")

; A polynomial cs ∈ ℤₚ[x] is represented by a list of coefficients,
; where the entry at index k is the coefficient of xᵏ.

; Definition disabled for better abstraction in proofs.
(defund polyp (cs p)
  (declare (xargs :guard (posp p)))
  (pfield::all-fep cs p))

(defun monomialp (cs p)
  (and (polyp cs p) (singleton cs)))

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
  (drop-vals-from-end 0 cs))

(defun poly-deg (cs)
  (let ((nf (poly-nf cs)))
    (if (nilp nf) :neginf (1- (len nf)))))

(defun poly-scale (c cs p)
  (declare (xargs :guard
    (and (posp p)
         (pfield::fep c p)
         (polyp cs p)))
  )
  (pfield::mapmul c cs p))

; Let us call multiplying cs ∈ ℤₚ[x] by (powers of) x, "shifting" cs.
(defun poly-shift (n cs)
  (declare (xargs :guard (natp n)))
  (if (zp n) cs (cons 0 (poly-shift (1- n) cs))))

; Doesn't trim trailing zeros
(defun poly+ (as bs p)
  (declare (xargs :guard
    (and (posp p)
         (polyp as p)
         (polyp bs p)))
  )
  (if (and (polyp as p) (polyp bs p))
      (cond ((atom as) bs)
            ((atom bs) as)
            ((and (consp as) (consp bs))
              (cons (pfield::add (first as) (first bs) p)
                    (poly+ (rest as) (rest bs) p))))
      :[poly+]-bad-inputs))

; Need the following to prove the guard condition for poly*.
(defthm all-fep-poly+
  (implies (and (posp p)
                (pfield::all-fep as p)
                (pfield::all-fep bs p))
           (pfield::all-fep (poly+ as bs p) p)))

(defun poly*-ind (as bs)
  (declare (xargs :measure (+ (len as) (len bs))))
  (cond ((and (consp as) (consp bs))
         (and (poly*-ind (rest as) (rest bs))
              (poly*-ind (rest as) bs)
              (poly*-ind as (rest bs))))
        (t t)))

(defun poly* (as bs p)
  (declare (xargs
    :guard
      (and (posp p)
           (polyp as p)
           (polyp bs p))
    :guard-hints
      (("Goal" :induct (poly*-ind as bs))))
  )
  (if (and (polyp as p) (polyp bs p))
      (cond ((or (atom as) (atom bs)) nil)
            ((and (consp as) (consp bs))
              (poly+ (poly-scale (first as) bs p)
                     (poly-shift 1 (poly* (rest as) bs p))
                     p)))
      :[poly*]-bad-inputs))

(defun poly-neg (cs p)
  (pfield::mapneg cs p))

(defun poly- (as bs p)
  (poly+ as (poly-neg bs p) p))


;; === Closure under operations ===

(defthm polyp-nf
  (implies (polyp cs p) (polyp (poly-nf cs) p))
  :rule-classes :type-prescription)

(defthm polyp-shift
  (implies (and (natp n) (posp p) (polyp cs p))
           (polyp (poly-shift n cs) p))
  :rule-classes :type-prescription)

(defthm poly-scale-closed
  (implies (and (posp p) (pfield::fep c p) (polyp cs p))
           (polyp (poly-scale c cs p) p))
  :rule-classes :type-prescription)

(defthm poly+-closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly+ as bs p) p))
  :rule-classes :type-prescription)

(defthm poly*-closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly* as bs p) p))
  :rule-classes :type-prescription)

(defthm poly-neg-closed
  (implies (and (posp p) (polyp cs p))
           (polyp (poly-neg cs p) p))
  :rule-classes :type-prescription)

(defthm poly--closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly- as bs p) p))
  :rule-classes :type-prescription)


;; ==== Reasoning about polynomials ====

; The definition of `polyp` is disabled by default in lieu of more
; abstract "type" reasoning (by the closure rules above). This is not
; always enough, and we sometimes still require certain "lower-level"
; properties of the definition.

; We record these rules here. Some of them are mathematical, and some
; are more "operational" and abstraction-breaking, i.e. have to do
; with properties of the list representation.

; More type reasoning: `rest` "downshifts" a polynomial.
(defthm polyp-rest
  (implies (polyp cs p) (polyp (rest cs) p))
  :rule-classes :type-prescription)

; This one is a rewrite rule and not a type prescription rule for two reasons:
; 1. Heuristically, it has to be a rewrite rule for the proof of poly*-comm in
; polynomial-thms.lisp to go through.
; 2. In principle, we do not want "type" reasoning to prove `polyp` for low-
; level properties of the list representations.
; In reality, (2) is a post-hoc justification of the real reason, which is (1).
(defthm polyp-cons
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p))
           (polyp (cons c cs) p)))

; all-fep ensures that cs is a true list.
(defthm polyp-true-listp
  (implies (polyp cs p) (true-listp cs))
  :rule-classes :forward-chaining)

(defthm polyp-first
  (implies (and (polyp cs p) (consp cs))
           (pfield::fep (first cs) p))
  :rule-classes :forward-chaining)

(defthm polyp-not-consp-is-nil
  (implies (and (polyp cs p) (not (consp cs)))
           (equal cs nil))
  :rule-classes :forward-chaining)

; "Fallback":
(defthm polyp-intro
  (implies (and (posp p) (pfield::all-fep cs p))
           (polyp cs p)))

)