;;; Lists of prime field elements
; Used to define univariate polynomials.

(ld "package.lsp")

(ld "prime-fields.lisp")

(ld "../prelude.lisp")

(in-package "PFIELDLIST")

; Note that in contrast to `pfield::fe-listp`,
; `all-fep xs p` does not guard `p` to be prime.
(defun all-fep (xs p)
  (declare (xargs :guard (posp p)))
  (or (acl2::nilp xs)
      (and (acl2::true-consp xs)
           (pfield::fep (first xs) p)
           (all-fep (rest xs) p))))

(defun scale (c cs p)
  (declare (xargs :guard
    (and (integerp p)
         (pfield::fep c p)
         (all-fep cs p))))
  (if (consp cs)
      (cons (pfield::mul c (first cs) p)
            (scale c (rest cs) p))
      nil))

(defun neg (cs p)
  (declare (xargs :guard (and (posp p) (all-fep cs p))))
  (if (consp cs)
      (cons (pfield::neg (first cs) p)
            (neg (rest cs) p))
      nil))

(defun add (as bs p)
  (declare (xargs :guard
    (and (posp p)
         (all-fep as p)
         (all-fep bs p))))
  (cond ((atom as) bs)
        ((atom bs) as)
        ((and (consp as) (consp bs)
           (cons (pfield::add (first as) (first bs) p)
                 (add (rest as) (rest bs) p))))))

(defun sub (as bs p)
  (declare (xargs :guard
    (and (posp p)
         (all-fep as p)
         (all-fep bs p))))
  (add as (neg bs p) p))