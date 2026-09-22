;;; Univariate polynomials over prime fields ℤ_p := ℤ/pℤ.
;   A polynomial q ∈ ℤ_p[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

(ld "prelude.lisp")
(ld "prime-fields.lisp")

(defun all-fep (cs p)
  (declare (xargs :guard (posp p)))
  (or (nilp cs)
      (and (true-consp cs)
           (pfield::fep (first cs) p)
           (all-fep (rest cs) p))))

(defthm cons-all-fep
  (implies (and (pfield::fep c p)
                (all-fep cs p))
           (all-fep (cons c cs) p)))

(defun polyp (cs p)
  (declare (xargs :guard (posp p)))
  (all-fep cs p))

(defun zeropoly () nil)
(defun onepoly () '(1))

; Removes trailing zeros.
(defun poly-trim (cs)
  (drop-vals-from-end 0 cs))

; Recognizes *any* list of zeroes
(defun zeropolyp (cs p)
  (and (polyp cs p) (all-equalp 0 cs)))

(defun nonzeropolyp (cs p)
  (and (polyp cs p) (not (all-equalp 0 cs))))

(defun poly-deg (cs)
  (let ((ds (poly-trim cs)))
    (if (endp ds) :neginf (1- (len ds)))))

(defun raise-deg (n cs)
  (declare (xargs :guard (natp n)))
  (append (repeat n 0) cs))

(defun mapmul (c cs p)
  (declare (xargs :guard (and (posp p)
                              (pfield::fep c p)
                              (all-fep cs p))))
  (if (consp cs)
      (cons (pfield::mul c (first cs) p) (mapmul c (rest cs) p))
      nil))

(defthm all-fep-mapmul
  (implies (posp p)
           (all-fep (mapmul c cs p) p)))

(defun scale-poly (c cs p)
  (declare (xargs :guard (and (posp p)
                              (pfield::fep c p)
                              (polyp cs p))))
  (mapmul c cs p))

; Doesn't trim trailing zeros
(defun poly+ (as bs p)
  (declare (xargs :guard (and (posp p)
                              (polyp as p)
                              (polyp bs p))))
  (cond ((atom as) (true-list-fix bs))
        ((atom bs) (true-list-fix as))
        ((and (consp as) (consp bs))
          (cons (pfield::add (first as) (first bs) p)
                (poly+ (rest as) (rest bs) p))
        )))

(defthm all-fep-poly+
  (implies (and (posp p) (all-fep as p) (all-fep bs p))
           (all-fep (poly+ as bs p) p)))

(defun poly* (as bs p)
  (declare (xargs :guard (and (posp p)
                              (polyp as p)
                              (polyp bs p))))
  (cond ((or (atom as) (atom bs)) nil)
        ((and (consp as) (consp bs))
          (let ((a0 (first as)) (aas (rest as))
                (b0 (first bs)) (bbs (rest bs)))
            (cons (pfield::mul a0 b0 p)
                  (poly+ (poly+ (scale-poly a0 bbs p)
                                (scale-poly b0 aas p)
                                p)
                         (raise-deg 1 (poly* aas bbs p))
                         p)))
        )))

#|
(defun poly-neg (p) (map- p))
(defun poly- (p q) (poly+ p (poly-neg q)))
|#