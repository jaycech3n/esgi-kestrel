(ld "pfieldlist.lisp")

(in-package "PFIELDLIST")

;; ==== Closure ====

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

(defthm all-fep-dropvals
  (implies (all-fep xs p)
           (all-fep (acl2::dropvals v xs) p)))

(defthm all-fep-scale
  (implies (posp p)
           (all-fep (scale c cs p) p)))

(defthm all-fep-neg
  (implies (posp p)
           (all-fep (neg cs p) p)))

(defthm all-fep-add
  (implies (and (posp p)
                (all-fep as p)
                (all-fep bs p))
           (all-fep (add as bs p) p)))

;; ==== Lengths ====

(defthm scale-len
  (equal (len (scale c cs p)) (len cs)))

(defthm neg-len
  (equal (len (neg cs p)) (len cs)))

(defthm add-len
  (equal (len (add as bs p))
         (max (len as) (len bs))))

;; ==== Equations ====

(defthm scale-0-all-equal-0
  (acl2::all-equalp 0 (scale 0 cs p))
  :hints (("Goal" :in-theory (disable acl2::all-equalp))))

; (defthmd scale-0-eq-repeat-0
;   (equal (scale 0 cs p)
;          (acl2::repeat (len cs) 0))
;   :hints (("Goal" :in-theory (enable acl2::repeat))))

(defthmd scale-append-eq-append-scales
  (equal (scale c (append as bs) p)
         (append (scale c as p) (scale c bs p))))

(defthmd rev-scale-eq-scale-rev
  (equal (acl2::rev (scale c cs p))
         (scale c (acl2::rev cs) p))
  :hints (("Goal"
    :in-theory (enable acl2::repeat scale-append-eq-append-scales))))