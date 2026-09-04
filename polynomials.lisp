;;; Univariate polynomials over R := ℤ or ℤ/nℤ.
;   A polynomial p ∈ R[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

; Some basics of polynomials are already defined here
(include-book "nonstd/polynomials/polynomial-defuns" :dir :system)
(include-book "nonstd/polynomials/polynomial-lemmas" :dir :system)

(ld "prelude.lisp")

;; General

(defun polyp (as) (integer-listp as))

(defun zeropoly () nil)
(defun onepoly () '(1))

; Removes trailing zeros.
(defun poly-normed (p)
  (if (polyp p)
      (drop-vals-from-end 0 p)
      :error[poly-normed][arg-not-poly))

; Recognizes *any* list of zeroes
(defun zeropolyp (p)
  (and (polyp p)
       (all-equalp-nofix 0 p)))

(defun nonzeropolyp (p)
  (and (polyp p)
       (not (all-equalp-nofix 0 p))))

(defun poly-deg (p)
  (let ((q (poly-normed p)))
    (if (endp q)
        :neginf
        (nat-pred (len q)))))

; Multiply by x
(defun poly*x (p) (cons 0 p))


;; ℤ[x]

(defun poly+ (p q) (polynomial-+ p q))
(defun poly* (p q) (polynomial-* p q))

(defun poly-neg (p) (map- p))
(defun poly- (p q) (poly+ p (poly-neg q)))


;; (ℤ/nℤ)[x]

(defun polymod+ (n p q) (mapmod n (poly+ p q)))
(defun polymod* (n p q) (mapmod n (poly* p q)))
(defun polymod-neg (n p) (mapmod n (poly-neg p)))
(defun polymod- (n p q) (mapmod n (poly- p q)))
