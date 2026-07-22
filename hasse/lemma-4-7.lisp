(ld "lemma-4-5.lisp")

; Prove that Ker(frob - 1) = E(fq).  Here subtraction is subtraction in
; the elliptic-curve group, not ACL2's arithmetic subtraction.

(defun frob-minus-one (point a b)
  (ec-add (frobenius-point point)
          (ec-neg point a b)
          a b))

(defthm ker-frob-sub-one
  (implies (and (on-curve-p point a b)
                (ec-group-p a b)
                (fq-elt-p a)
                (fq-elt-p b))
           (iff (equal (frob-minus-one point a b) :infinity)
                (fq-rational-point-p point a b)))
  :hints (("Goal"
           :use ((:instance ec-subtract-equal-iff
                            (point1 (frobenius-point point))
                            (point2 point))))))
