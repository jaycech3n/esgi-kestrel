;;; Univariate polynomials over R := ℤ or ℤ/nℤ.
;   A polynomial p ∈ R[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

(ld "prelude.lisp")
(ld "arithmetic.lisp")


;; ℤ[x]

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

(defun scale-poly (c p) (map* c p))

; Doesn't trim trailing zeros
(defun poly+ (p q)
  (cond ((not (and (polyp p) (polyp q)))
          :error[poly+][p-or-q-not-poly])
        ((not p) q)
        ((not q) p)
        (t
          (cons (+ (first p) (first q)) (poly+ (rest p) (rest q))))))

(defun poly* (p q)
  (cond ((not (and (polyp p) (polyp q)))
          :error[obv-comm-poly*][p-or-q-not-poly])
        ((not p) nil)
        ((not q) nil)
        (t
          (let ((a0 (first p)) (as (rest p))
                (b0 (first q)) (bs (rest q)))
            (cons (* a0 b0)
                  (poly+ (poly+ (scale-poly a0 bs)
                                (scale-poly b0 as))
                         (raise-deg 1 (poly* as bs)))))
          ; (poly+ (list (* (first p) (first q)))
          ; (poly+ (raise-deg 1 (scale-poly (rest q) (first p)))
          ; (poly+ (raise-deg 1 (scale-poly (rest p) (first q)))
          ;        (raise-deg 2 (poly* (rest p) (rest q))))))
          )))

(defun poly-neg (p) (map- p))
(defun poly- (p q) (poly+ p (poly-neg q)))


;; (ℤ/nℤ)[x]

(defun polymod+ (p q n) (mapmod (poly+ p q) n))
(defun polymod* (p q n) (mapmod (poly* p q) n))
(defun polymod-neg (p n) (mapmod (poly-neg p) n))
(defun polymod- (p q n) (mapmod (poly- p q) n))
