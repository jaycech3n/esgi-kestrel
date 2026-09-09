;;; Univariate polynomials over R := ℤ or ℤ/nℤ.
;   A polynomial p ∈ R[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

; Some basics of polynomials are already defined here
(include-book "nonstd/polynomials/polynomial-defuns" :dir :system)
(include-book "nonstd/polynomials/polynomial-lemmas" :dir :system)

(ld "prelude.lisp")
(ld "arithmetic.lisp")


;; General

(defun polyp (as) (integer-listp as))

(defun zeropoly () nil)
(defun onepoly () '(1))

; Removes trailing zeros.
(defun poly-trim (p)
  (if (polyp p)
      (drop-vals-from-end 0 p)
      :error[poly-trim][arg-not-poly))

; Recognizes *any* list of zeroes
(defun zeropolyp (p)
  (and (polyp p)
       (all-equalp 0 p)))

(defun nonzeropolyp (p)
  (and (polyp p)
       (not (all-equalp 0 p))))

(defun poly-deg (p)
  (let ((q (poly-trim p)))
    (if (endp q)
        :neginf
        (nat-pred (len q)))))

(defun raise-deg (n p) (append (repeat n 0) p))


;; ℤ[x]

(defun poly+ (p q) (polynomial-+ p q))
(defun poly* (p q) (poly-trim (polynomial-* p q)))
  ; poly* *needs* to be trimmed to be commutative

(defun poly-neg (p) (map- p))
(defun poly- (p q) (poly+ p (poly-neg q)))


;; (ℤ/nℤ)[x]

(defun polymod+ (p q n) (mapmod (poly+ p q) n))
(defun polymod* (p q n) (mapmod (poly* p q) n))
(defun polymod-neg (p n) (mapmod (poly-neg p) n))
(defun polymod- (p q n) (mapmod (poly- p q) n))
