(ld "kestrel/prime-fields/package.lsp"   :dir :system)
(include-book "kestrel/prime-fields/top" :dir :system)

; --- Recognizer of lists of prime field elements ---
; Used to define polynomials over prime fields.

(defun all-fep (xs p)
  (declare (xargs :guard (posp p)))
  (or (nilp xs)
      (and (true-consp xs)
           (pfield::fep (first xs) p)
           (all-fep (rest xs) p))))

(defthm all-fep-cons
  (implies (and (pfield::fep x p)
                (all-fep xs p))
           (all-fep (cons x xs) p)))

(defthm all-fep-rest
  (implies (all-fep xs p)
           (all-fep (rest xs) p)))

(defthm all-fep-append
  (implies (and (all-fep xs p) (all-fep ys p))
           (all-fep (append xs ys) p)))

(defthm all-fep-rev
  (implies (all-fep xs p)
           (all-fep (rev xs) p)))

(defthm all-fep-repeat
  (implies (pfield::fep x p)
           (all-fep (repeat n x) p))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm all-fep-drop-vals
  (implies (all-fep xs p)
           (all-fep (drop-vals v xs) p)))


; --- Maps ---

(defun mapmul (c cs p)
  (declare (xargs
    :guard (and (posp p)
                (pfield::fep c p)
                (all-fep cs p))))
  (if (consp cs)
      (cons (pfield::mul c (first cs) p)
            (mapmul c (rest cs) p))
      nil))

(defthm all-fep-mapmul
  (implies (posp p)
           (all-fep (mapmul c cs p) p)))

(defun mapneg (cs p)
  (declare (xargs
    :guard (and (posp p)
                (all-fep cs p))
  ))
  (if (consp cs)
      (cons (pfield::neg (first cs) p)
            (mapneg (rest cs) p))
      nil))