(ld "kestrel/prime-fields/package.lsp"   :dir :system)
(include-book "kestrel/prime-fields/top" :dir :system)

(ld "../prelude.lisp")

(in-package "PFIELD")

;; ==== Lists of prime field elements ====

; Note that in contrast to `pfield::fe-listp`,
; `all-fep xs p` does not guard `p` to be prime.
(defun all-fep (xs p)
  (declare (xargs :guard (posp p)))
  (or (acl2::nilp xs)
      (and (acl2::true-consp xs)
           (pfield::fep (first xs) p)
           (all-fep (rest xs) p))))

; --- Maps ---

(defun mapmul (c cs p)
  (declare (xargs :guard
    (and (integerp p)
         (pfield::fep c p)
         (all-fep cs p))))
  (if (consp cs)
      (cons (pfield::mul c (first cs) p)
            (mapmul c (rest cs) p))
      nil))

(defun mapneg (cs p)
  (declare (xargs :guard (and (posp p) (all-fep cs p))))
  (if (consp cs)
      (cons (pfield::neg (first cs) p)
            (mapneg (rest cs) p))
      nil))

; --- Zips ---

(defun zipadd (as bs p)
  (declare (xargs :guard
    (and (posp p)
         (all-fep as p)
         (all-fep bs p))))
  (cond ((atom as) bs)
        ((atom bs) as)
        ((and (consp as) (consp bs)
           (cons (pfield::add (first as) (first bs) p)
                 (zipadd (rest as) (rest bs) p))))))

(defun zipsub (as bs p)
  (declare (xargs :guard
    (and (posp p)
         (all-fep as p)
         (all-fep bs p))))
  (zipadd as (mapneg bs p) p))