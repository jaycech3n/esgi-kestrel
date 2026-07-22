; Washington, Lemma 4.5: Frobenius preserves E and its fixed points are E(F_q).

(in-package "ACL2")
(ld "frobenius.lisp")

(defthm frobenius-preserves-affine-curve
  (implies (and (fe-p x) (fe-p y)
                (fq-elt-p a) (fq-elt-p b)
                (equal (fsquare y) (curve-rhs x a b)))
           (equal (fsquare (frob y))
                  (curve-rhs (frob x) a b)))
  :hints (("Goal"
           :use ((:instance frob-preserves-equality
                            (x (fsquare y))
                            (y (curve-rhs x a b)))))))

(defthm lemma-4-5-part-1
  (implies (and (on-curve-p point a b)
                (fq-elt-p a) (fq-elt-p b))
           (on-curve-p (frobenius-point point) a b)))

(defthm affine-point-fixed-by-frobenius
  (implies (and (fe-p x) (fe-p y))
           (iff (equal (frobenius-point (ec-affine-point x y))
                       (ec-affine-point x y))
                (and (fq-elt-p x) (fq-elt-p y)))))

(defthm lemma-4-5-part-2
  (implies (on-curve-p point a b)
           (iff (equal (frobenius-point point) point)
                (fq-rational-point-p point a b))))

(defthm lemma-4-5
  (implies (and (on-curve-p point a b)
                (fq-elt-p a) (fq-elt-p b))
           (and (on-curve-p (frobenius-point point) a b)
                (iff (equal (frobenius-point point) point)
                     (fq-rational-point-p point a b)))))
