;;; Univariate polynomials over R := ℤ or ℤ/nℤ.
;   A polynomial p ∈ R[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

; Some basics of polynomials are already defined here
(include-book "nonstd/polynomials/polynomial-defuns" :dir :system)
(include-book "nonstd/polynomials/polynomial-lemmas" :dir :system)

(ld "prelude.lisp")

;; General

(defun polyp (coeffs) (integer-listp coeffs))

(defun zeropoly () nil)
(defun onepoly () '(1))

; Removes trailing zeros.
(defun poly-normed (p) (drop-vals-from-end 0 p))

(defun zeropolyp (p) (endp (poly-normed p)))

(defun poly-deg (p)
  (let ((np (poly-normed p)))
    (if (endp np)
        :neginf
        (nat-pred (len np)))))

;; ℤ[x]

(defun poly+ (p q) (polynomial-+ p q))
(defun poly* (p q) (polynomial-* p q))

(defun poly-neg (p) (map- p))
(defun poly- (p q) (poly+ p (poly-neg q)))

;; (ℤ/nℤ)[x]

(defun polymod+ (n p q) (mapmod n (poly+ p q)))
(defun polymod* (n p q) (mapmod n (poly* p q)))
(defun polymod- (n p q) (mapmod n (poly- p q)))