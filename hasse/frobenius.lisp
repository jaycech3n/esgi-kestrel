; Frobenius on points of a short Weierstrass curve.

(in-package "ACL2")
(ld "elliptic-curve.lisp")

(defun frobenius-point (point)
  (if (ec-infinity-p point)
      :infinity
    (ec-affine-point (frob (ec-x point))
                     (frob (ec-y point)))))

(defthm frob-of-square
  (implies (fe-p x)
           (equal (frob (fsquare x)) (fsquare (frob x)))))

(defthm frob-of-cube
  (implies (fe-p x)
           (equal (frob (fcube x)) (fcube (frob x)))))

(defthm frob-of-curve-rhs
  (implies (and (fe-p x) (fq-elt-p a) (fq-elt-p b))
           (equal (frob (curve-rhs x a b))
                  (curve-rhs (frob x) a b))))

(defthm frob-preserves-equality
  (implies (equal x y) (equal (frob x) (frob y)))
  :rule-classes nil)
