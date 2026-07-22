; Lemma 4.5 from Lawrence C. Washington, Elliptic Curves:
; Number Theory and Cryptography.
;
; This book deliberately works over an abstract ambient field.  The constrained
; function FROB is intended eventually to be instantiated by x |-> x^q.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; The small part of the finite-field/Frobenius interface needed by Lemma 4.5.
; -----------------------------------------------------------------------------

(encapsulate
 (((fe-p *) => *)
  ((fq-elt-p *) => *)
  ((fadd * *) => *)
  ((fmul * *) => *)
  ((frob *) => *))

 ; A one-element local model witnesses consistency of the constraints.  These
 ; definitions are hidden outside this encapsulate; they are not the eventual
 ; implementation of finite fields.
 (local (defun fe-p (x) (equal x nil)))
 (local (defun fq-elt-p (x) (equal x nil)))
 (local (defun fadd (x y) (declare (ignore x y)) nil))
 (local (defun fmul (x y) (declare (ignore x y)) nil))
 (local (defun frob (x) (declare (ignore x)) nil))

 (defthm fq-elements-are-ambient-elements
   (implies (fq-elt-p x)
            (fe-p x)))

 (defthm fadd-closed
   (implies (and (fe-p x) (fe-p y))
            (fe-p (fadd x y))))

 (defthm fmul-closed
   (implies (and (fe-p x) (fe-p y))
            (fe-p (fmul x y))))

 (defthm frob-closed
   (implies (fe-p x)
            (fe-p (frob x))))

 (defthm frob-of-add
   (implies (and (fe-p x) (fe-p y))
            (equal (frob (fadd x y))
                   (fadd (frob x) (frob y)))))

 (defthm frob-of-mul
   (implies (and (fe-p x) (fe-p y))
            (equal (frob (fmul x y))
                   (fmul (frob x) (frob y)))))

 ; The two directions of the fixed-field theorem are kept as separate rewrite
 ; rules.  This avoids a rewrite loop that a single IFF rule can cause.
 (defthm frob-fixes-fq-elements
   (implies (fq-elt-p x)
            (equal (frob x) x)))

 (defthm frob-fixed-elements-are-fq-elements
   (implies (and (fe-p x)
                 (equal (frob x) x))
            (fq-elt-p x))))

; -----------------------------------------------------------------------------
; Short Weierstrass curves and their points.
; -----------------------------------------------------------------------------

(defun fsquare (x)
  (fmul x x))

(defun fcube (x)
  (fmul (fmul x x) x))

(defun ec-infinity-p (point)
  (equal point :infinity))

(defun ec-affine-point (x y)
  (list :affine x y))

(defun ec-affine-point-p (point)
  (and (consp point)
       (equal (car point) :affine)
       (consp (cdr point))
       (consp (cddr point))
       (null (cdddr point))
       (fe-p (cadr point))
       (fe-p (caddr point))))

(defun ec-x (point)
  (cadr point))

(defun ec-y (point)
  (caddr point))

(defun ec-point-p (point)
  (or (ec-infinity-p point)
      (ec-affine-point-p point)))

(defun curve-rhs (x a b)
  (fadd (fcube x)
        (fadd (fmul a x) b)))

(defun on-curve-p (point a b)
  (and (ec-point-p point)
       (or (ec-infinity-p point)
           (equal (fsquare (ec-y point))
                  (curve-rhs (ec-x point) a b)))))

(defun fq-rational-point-p (point a b)
  (and (on-curve-p point a b)
       (or (ec-infinity-p point)
           (and (fq-elt-p (ec-x point))
                (fq-elt-p (ec-y point))))))

(defun frobenius-point (point)
  (if (ec-infinity-p point)
      :infinity
    (ec-affine-point (frob (ec-x point))
                     (frob (ec-y point)))))

; -----------------------------------------------------------------------------
; Abstract group law on E over the algebraic closure.
; -----------------------------------------------------------------------------
;
; The coordinate formula for the chord-and-tangent law needs substantially
; more of the ambient-field development (zero, negation and division).  Until
; that is available, expose exactly the group interface used below.  The local
; definitions are only a consistency witness; EC-ADD and EC-NEG remain
; constrained functions outside the encapsulate.

(encapsulate
 (((ec-add * * * *) => *)
  ((ec-neg * * *) => *)
  ((ec-group-p * *) => *))

 (local (defun ec-neg (point a b)
          (declare (ignore a b))
          point))

 (local (defun ec-add (point1 point2 a b)
          (declare (ignore point1 point2 a b))
          :infinity))

 ; A false local recognizer makes the constraints a conservative extension.
 ; Later, the concrete chord-and-tangent development should prove EC-GROUP-P
 ; for every nonsingular pair (A,B).
 (local (defun ec-group-p (a b)
          (declare (ignore a b))
          nil))

 (defthm ec-add-closed
   (implies (and (ec-group-p a b)
                 (on-curve-p point1 a b)
                 (on-curve-p point2 a b))
            (on-curve-p (ec-add point1 point2 a b) a b)))

 (defthm ec-add-identity
   (implies (and (ec-group-p a b)
                 (on-curve-p point a b))
            (and (equal (ec-add :infinity point a b) point)
                 (equal (ec-add point :infinity a b) point))))

 (defthm ec-add-associative
   (implies (and (ec-group-p a b)
                 (on-curve-p point1 a b)
                 (on-curve-p point2 a b)
                 (on-curve-p point3 a b))
            (equal (ec-add (ec-add point1 point2 a b) point3 a b)
                   (ec-add point1 (ec-add point2 point3 a b) a b))))

 (defthm ec-add-inverse
   (implies (and (ec-group-p a b)
                 (on-curve-p point a b))
            (and (on-curve-p (ec-neg point a b) a b)
                 (equal (ec-add point (ec-neg point a b) a b)
                        :infinity)
                 (equal (ec-add (ec-neg point a b) point a b)
                        :infinity))))

 )

; This is a consequence of the group laws, rather than an additional
; constraint on EC-ADD and EC-NEG.  It is the cancellation fact needed to
; identify the kernel of Frobenius minus the identity.
(defthm ec-subtract-equal-iff
  (implies (and (ec-group-p a b)
                (on-curve-p point1 a b)
                (on-curve-p point2 a b))
           (iff (equal (ec-add point1 (ec-neg point2 a b) a b)
                       :infinity)
                (equal point1 point2)))
  :hints (("Goal"
           :in-theory (disable on-curve-p
                               ec-add-associative
                               ec-add-identity
                               ec-add-inverse)
           :use ((:instance ec-add-associative
                            (point1 point1)
                            (point2 (ec-neg point2 a b))
                            (point3 point2))
                 (:instance ec-add-identity (point point1))
                 (:instance ec-add-identity (point point2))
                 (:instance ec-add-inverse (point point2))))))

; -----------------------------------------------------------------------------
; Algebraic normalization lemmas used in the curve calculation.
; -----------------------------------------------------------------------------

(defthm frob-of-square
  (implies (fe-p x)
           (equal (frob (fsquare x))
                  (fsquare (frob x)))))

(defthm frob-of-cube
  (implies (fe-p x)
           (equal (frob (fcube x))
                  (fcube (frob x)))))

(defthm frob-of-curve-rhs
  (implies (and (fe-p x)
                (fq-elt-p a)
                (fq-elt-p b))
           (equal (frob (curve-rhs x a b))
                  (curve-rhs (frob x) a b))))

(defthm frob-preserves-equality
  (implies (equal x y)
           (equal (frob x) (frob y)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Washington, Lemma 4.5(1): Frobenius maps E over the algebraic closure to E.
; -----------------------------------------------------------------------------

(defthm frobenius-preserves-affine-curve
  (implies (and (fe-p x)
                (fe-p y)
                (fq-elt-p a)
                (fq-elt-p b)
                (equal (fsquare y)
                       (curve-rhs x a b)))
           (equal (fsquare (frob y))
                  (curve-rhs (frob x) a b)))
  :hints (("Goal"
           :use ((:instance frob-preserves-equality
                            (x (fsquare y))
                            (y (curve-rhs x a b)))))))

(defthm lemma-4-5-part-1
  (implies (and (on-curve-p point a b)
                (fq-elt-p a)
                (fq-elt-p b))
           (on-curve-p (frobenius-point point) a b)))

; -----------------------------------------------------------------------------
; Washington, Lemma 4.5(2): the fixed points are exactly E(F_q).
; -----------------------------------------------------------------------------

(defthm affine-point-fixed-by-frobenius
  (implies (and (fe-p x) (fe-p y))
           (iff (equal (frobenius-point (ec-affine-point x y))
                       (ec-affine-point x y))
                (and (fq-elt-p x)
                     (fq-elt-p y)))))

(defthm lemma-4-5-part-2
  (implies (on-curve-p point a b)
           (iff (equal (frobenius-point point) point)
                (fq-rational-point-p point a b))))

; A combined formulation mirroring the two numbered claims in the book.
(defthm lemma-4-5
  (implies (and (on-curve-p point a b)
                (fq-elt-p a)
                (fq-elt-p b))
           (and (on-curve-p (frobenius-point point) a b)
                (iff (equal (frobenius-point point) point)
                     (fq-rational-point-p point a b)))))
