(ld "prime-fields.lisp")

(in-package "PFIELD")

; --- Closure properties ---

(defthm all-fep-cons
  (implies (and (pfield::fep x p)
                (all-fep xs p))
           (all-fep (cons x xs) p)))

(defthm all-fep-rest
  (implies (all-fep xs p)
           (all-fep (rest xs) p)))

(defthm all-fep-append
  (implies (and (all-fep xs p) (all-fep ys p))
           (all-fep (acl2::append xs ys) p)))

(defthm all-fep-rev
  (implies (all-fep xs p)
           (all-fep (acl2::rev xs) p)))

(defthm all-fep-repeat
  (implies (pfield::fep x p)
           (all-fep (acl2::repeat n x) p))
  :hints (("Goal" :in-theory (enable acl2::repeat))))

(defthm all-fep-drop-vals
  (implies (all-fep xs p)
           (all-fep (acl2::drop-vals v xs) p)))

(defthm all-fep-mapmul
  (implies (posp p)
           (all-fep (mapmul c cs p) p)))

(defthm all-fep-mapneg
  (implies (posp p)
           (all-fep (mapneg cs p) p)))

(defthm all-fep-zipadd
  (implies (and (posp p)
                (all-fep as p)
                (all-fep bs p))
           (all-fep (zipadd as bs p) p)))


; --- Lengths ---

(defthm mapmul-len
  (equal (len (mapmul c cs p)) (len cs)))

(defthm mapneg-len
  (equal (len (mapneg cs p)) (len cs)))

(defthm zipadd-len
  (equal (len (zipadd as bs p))
         (max (len as) (len bs))))


; --- Equalities ---

(defthmd mapmul-0
  (equal (mapmul 0 cs p)
         (acl2::repeat (len cs) 0))
  :hints (("Goal" :in-theory (enable acl2::repeat))))