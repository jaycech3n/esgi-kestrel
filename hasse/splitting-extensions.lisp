; Finite splitting certificates: the executable replacement for referring to
; all elements of an algebraic closure at once.

(in-package "ACL2")

(defun sf-poly-eval-aux (coeffs x power field)
  (if (endp coeffs)
      (ff-zero field)
    (ff-add (ff-mul (car coeffs) power field)
            (sf-poly-eval-aux (cdr coeffs) x
                              (ff-mul power x field) field)
            field)))

(defun sf-poly-eval (coeffs x field)
  (sf-poly-eval-aux coeffs x (ff-one field) field))

(defun all-ff-elements-p (xs field)
  (if (endp xs)
      t
    (and (ff-element-p (car xs) field)
         (all-ff-elements-p (cdr xs) field))))

(defun all-roots-p (roots poly field)
  (if (endp roots)
      t
    (and (equal (sf-poly-eval poly (car roots) field)
                (ff-zero field))
         (all-roots-p (cdr roots) poly field))))

(defun splitting-certificate (field roots)
  (list :splitting-certificate field roots))
(defun splitting-certificate-field (certificate) (cadr certificate))
(defun splitting-certificate-roots (certificate) (caddr certificate))

(defun splitting-certificate-p (poly certificate)
  (let ((field (splitting-certificate-field certificate))
        (roots (splitting-certificate-roots certificate)))
    (and (equal (car certificate) :splitting-certificate)
         (equal (len certificate) 3)
         (ff-field-p field)
         (true-listp roots)
         (all-ff-elements-p roots field)
         (all-roots-p roots poly field))))

(defun square-free-splitting-certificate-p (poly certificate)
  (and (splitting-certificate-p poly certificate)
       (no-duplicatesp-equal (splitting-certificate-roots certificate))
       (equal (len (splitting-certificate-roots certificate))
              (pf-poly-degree poly))))

(defthm square-free-certificate-root-count
  (implies (square-free-splitting-certificate-p poly certificate)
           (equal (len (splitting-certificate-roots certificate))
                  (pf-poly-degree poly))))
