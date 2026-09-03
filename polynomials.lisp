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

(defun zeropolyp (p)
  (and (polyp p)
       (endp (poly-normed p))))

(defun nonzeropolyp (p)
  (and (polyp p)
       (not (endp (poly-normed p)))))

(defthm zeropolyp-iff
  (implies (zeropolyp p)
           (or (endp p)
               (and (consp p)
                    (zerop (first p))
                    (zeropolyp (rest p))))))

(defthm not-zeropolyp-iff-nonzeropolyp
  (implies (polyp p)
           (iff (nonzeropolyp p)
                (not (zeropolyp p)))))

(defun poly-deg (p)
  (let ((q (poly-normed p)))
    (if (endp q)
        :neginf
        (nat-pred (len q)))))

;; ℤ[x]

(defun poly+ (p q) (polynomial-+ p q))
(defun poly* (p q) (polynomial-* p q))

(defun poly-neg (p) (map- p))
(defun poly- (p q) (poly+ p (poly-neg q)))

(defthm poly+-closed
  (implies (and (polyp p) (polyp q))
           (polyp (poly+ p q))))

(defthm poly*-nil
  (equal (poly* (cons a as) nil)
         (cons 0 (poly* as nil))))

(defthm scale-polynomial-closed
  (implies (and (integerp c)
                (polyp p))
           (polyp (scale-polynomial p c))))

(defthm cons-polyp-closed
  (implies (and (integerp a)
                (polyp p))
           (polyp (cons a p))))

;; (ℤ/nℤ)[x]

(defun polymod+ (n p q) (mapmod n (poly+ p q)))
(defun polymod* (n p q) (mapmod n (poly* p q)))
(defun polymod- (n p q) (mapmod n (poly- p q)))

(defthm polymod+-closed
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (polyp (polymod+ n p q))))

; (defthm polymod*-closed
;   (implies (and (integerp n)
;                 (polyp p)
;                 (polyp q))
;            (polyp (polymod* n p q)))
;   :hints
;     (("Goal" :induct (len q))))