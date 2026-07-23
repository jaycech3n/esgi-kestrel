; Short Weierstrass curves over explicit finite fields.

(in-package "ACL2")

(defun ffc-curve (a b) (list :short-weierstrass a b))
(defun ffc-a (curve) (cadr curve))
(defun ffc-b (curve) (caddr curve))
(defun ffc-infinity () :infinity)
(defun ffc-point (x y) (list :affine x y))
(defun ffc-x (point) (cadr point))
(defun ffc-y (point) (caddr point))

(defun ffc-square (x field) (ff-mul x x field))
(defun ffc-cube (x field) (ff-mul x (ff-mul x x field) field))

(defun ffc-curve-p (curve field)
  (and (equal (car curve) :short-weierstrass)
       (equal (len curve) 3)
       (ff-element-p (ffc-a curve) field)
       (ff-element-p (ffc-b curve) field)))

(defun ffc-on-curve-p (point curve field)
  (or (equal point (ffc-infinity))
      (and (equal (car point) :affine)
           (equal (len point) 3)
           (ff-element-p (ffc-x point) field)
           (ff-element-p (ffc-y point) field)
           (equal (ffc-square (ffc-y point) field)
                  (ff-add (ffc-cube (ffc-x point) field)
                          (ff-add (ff-mul (ffc-a curve) (ffc-x point) field)
                                  (ffc-b curve) field)
                          field)))))

(defun ffc-points-with-x (x ys curve field)
  (if (endp ys)
      nil
    (let ((point (ffc-point x (car ys))))
      (if (ffc-on-curve-p point curve field)
          (cons point (ffc-points-with-x x (cdr ys) curve field))
        (ffc-points-with-x x (cdr ys) curve field)))))

(defun ffc-affine-points (xs all-elements curve field)
  (if (endp xs)
      nil
    (append (ffc-points-with-x (car xs) all-elements curve field)
            (ffc-affine-points (cdr xs) all-elements curve field))))

(defun ffc-points (curve field)
  (let ((elements (ff-elements field)))
    (cons (ffc-infinity)
          (ffc-affine-points elements elements curve field))))

(defun ffc-frobenius-point (point field)
  (if (equal point (ffc-infinity))
      (ffc-infinity)
    (ffc-point (ff-frobenius (ffc-x point) field)
               (ff-frobenius (ffc-y point) field))))

(defun ffc-point-count (curve field)
  (len (ffc-points curve field)))

(defthm ffc-infinity-is-on-curve
  (ffc-on-curve-p (ffc-infinity) curve field))
