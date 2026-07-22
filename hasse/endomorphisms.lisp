; Rational endomorphisms and Washington, Proposition 2.21.
;
; The constrained "good fibre" interface records the concrete polynomial
; argument on pp. 53--54: for r_1=p/q, choose T=(a,b) so p-aq is square-free
; of degree deg(alpha), and its roots enumerate alpha^{-1}(T).  The list
; translation below is the group-theoretic passage from that fibre to Ker(alpha).

(in-package "ACL2")
(ld "elliptic-curve.lisp")
(ld "polynomials.lisp")

(encapsulate
 (((endomorphism-p * * *) => *)
  ((nonzero-endomorphism-p * * *) => *)
  ((separable-endomorphism-p *) => *)
  ((endo-apply * * * *) => *)
  ((endo-numerator *) => *)
  ((endo-denominator *) => *)
  ((endo-y-factor *) => *)
  ((endo-degree *) => *)
  ((endo-good-target * * *) => *)
  ((endo-good-preimage * * *) => *)
  ((endo-good-fiber-list * * *) => *))

 (local (defun endomorphism-p (alpha a b)
          (declare (ignore alpha a b)) nil))
 (local (defun nonzero-endomorphism-p (alpha a b)
          (declare (ignore alpha a b)) nil))
 (local (defun separable-endomorphism-p (alpha)
          (declare (ignore alpha)) nil))
 (local (defun endo-apply (alpha point a b)
          (declare (ignore alpha point a b)) :infinity))
 (local (defun endo-numerator (alpha) (declare (ignore alpha)) nil))
 (local (defun endo-denominator (alpha) (declare (ignore alpha)) nil))
 (local (defun endo-y-factor (alpha) (declare (ignore alpha)) nil))
 (local (defun endo-degree (alpha) (declare (ignore alpha)) 0))
 (local (defun endo-good-target (alpha a b)
          (declare (ignore alpha a b)) :infinity))
 (local (defun endo-good-preimage (alpha a b)
          (declare (ignore alpha a b)) :infinity))
 (local (defun endo-good-fiber-list (alpha a b)
          (declare (ignore alpha a b)) nil))

 (defthm endomorphism-maps-curve-to-curve
   (implies (and (endomorphism-p alpha a b)
                 (on-curve-p point a b))
            (on-curve-p (endo-apply alpha point a b) a b)))

 (defthm endomorphism-preserves-addition
   (implies (and (endomorphism-p alpha a b)
                 (ec-group-p a b)
                 (on-curve-p point1 a b)
                 (on-curve-p point2 a b))
            (equal (endo-apply alpha (ec-add point1 point2 a b) a b)
                   (ec-add (endo-apply alpha point1 a b)
                           (endo-apply alpha point2 a b) a b))))

 (defthm endomorphism-preserves-infinity
   (implies (and (endomorphism-p alpha a b) (ec-group-p a b))
            (equal (endo-apply alpha :infinity a b) :infinity)))

 ; This is the explicit polynomial/root-counting result in Washington's proof.
 ; It is kept as a separate boundary so it can later be proved from the
 ; definitions in polynomials.lisp without changing downstream theorems.
 (defthm good-fiber-has-degree-many-points
   (implies (and (endomorphism-p alpha a b)
                 (nonzero-endomorphism-p alpha a b)
                 (separable-endomorphism-p alpha))
            (equal (len (endo-good-fiber-list alpha a b))
                   (endo-degree alpha))))

 (defthm good-preimage-lies-over-good-target
   (implies (and (endomorphism-p alpha a b)
                 (nonzero-endomorphism-p alpha a b)
                 (separable-endomorphism-p alpha))
            (and (on-curve-p (endo-good-preimage alpha a b) a b)
                 (equal (endo-apply alpha
                                    (endo-good-preimage alpha a b) a b)
                        (endo-good-target alpha a b))))))
(defun endo-kernel-point-p (alpha point a b)
  (and (on-curve-p point a b)
       (equal (endo-apply alpha point a b) :infinity)))

(defun endo-kernel-list (alpha a b)
  (ec-translate-list
   (endo-good-fiber-list alpha a b)
   (ec-neg (endo-good-preimage alpha a b) a b)
   a b))

(defun endo-kernel-cardinality (alpha a b)
  (len (endo-kernel-list alpha a b)))

(defthm len-of-endo-kernel-list
  (equal (len (endo-kernel-list alpha a b))
         (len (endo-good-fiber-list alpha a b))))

(defun-sk endo-kernel-list-is-complete-p (alpha a b)
  (forall point
          (iff (member-equal point (endo-kernel-list alpha a b))
               (endo-kernel-point-p alpha point a b))))

; Washington, Proposition 2.21 (separable case).  The semantic obligation that
; ENDO-KERNEL-LIST enumerates exactly ENDO-KERNEL-POINT-P is kept explicit as
; a hypothesis until the fibre-translation bijection is formalized.
(defthm proposition-2-21-separable
  (implies (and (endomorphism-p alpha a b)
                (nonzero-endomorphism-p alpha a b)
                (separable-endomorphism-p alpha)
                (endo-kernel-list-is-complete-p alpha a b))
           (equal (endo-degree alpha)
                  (endo-kernel-cardinality alpha a b))))
