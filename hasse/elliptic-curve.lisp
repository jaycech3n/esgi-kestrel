; Short Weierstrass curves and their abstract group law.

(in-package "ACL2")
(ld "field.lisp")

(defun ec-infinity-p (point) (equal point :infinity))
(defun ec-affine-point (x y) (list :affine x y))

(defun ec-affine-point-p (point)
  (and (consp point)
       (equal (car point) :affine)
       (consp (cdr point))
       (consp (cddr point))
       (null (cdddr point))
       (fe-p (cadr point))
       (fe-p (caddr point))))

(defun ec-x (point) (cadr point))
(defun ec-y (point) (caddr point))

(defun ec-point-p (point)
  (or (ec-infinity-p point) (ec-affine-point-p point)))

(defun curve-rhs (x a b)
  (fadd (fcube x) (fadd (fmul a x) b)))

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

(encapsulate
 (((ec-add * * * *) => *)
  ((ec-neg * * *) => *)
  ((ec-group-p * *) => *))

 (local (defun ec-neg (point a b)
          (declare (ignore a b)) point))
 (local (defun ec-add (point1 point2 a b)
          (declare (ignore point1 point2 a b)) :infinity))
 (local (defun ec-group-p (a b)
          (declare (ignore a b)) nil))

 (defthm ec-add-closed
   (implies (and (ec-group-p a b)
                 (on-curve-p point1 a b)
                 (on-curve-p point2 a b))
            (on-curve-p (ec-add point1 point2 a b) a b)))

 (defthm ec-add-identity
   (implies (and (ec-group-p a b) (on-curve-p point a b))
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
   (implies (and (ec-group-p a b) (on-curve-p point a b))
            (and (on-curve-p (ec-neg point a b) a b)
                 (equal (ec-add point (ec-neg point a b) a b) :infinity)
                 (equal (ec-add (ec-neg point a b) point a b) :infinity)))))

(defthm ec-subtract-equal-iff
  (implies (and (ec-group-p a b)
                (on-curve-p point1 a b)
                (on-curve-p point2 a b))
           (iff (equal (ec-add point1 (ec-neg point2 a b) a b)
                       :infinity)
                (equal point1 point2)))
  :hints (("Goal"
           :in-theory (disable on-curve-p ec-add-associative
                               ec-add-identity ec-add-inverse)
           :use ((:instance ec-add-associative
                            (point2 (ec-neg point2 a b))
                            (point3 point2))
                 (:instance ec-add-identity (point point1))
                 (:instance ec-add-identity (point point2))
                 (:instance ec-add-inverse (point point2))))))

(defun ec-translate-list (points offset a b)
  (if (endp points)
      nil
    (cons (ec-add (car points) offset a b)
          (ec-translate-list (cdr points) offset a b))))

(defthm len-of-ec-translate-list
  (equal (len (ec-translate-list points offset a b))
         (len points)))
