; Univariate polynomials over the ambient algebraic closure.
;
; Coefficients are stored from constant term upward.  The root-list theorem is
; the algebraic-closure boundary needed by Washington's Proposition 2.21.

(in-package "ACL2")

(defun field-polynomial-p (poly)
  (if (consp poly)
      (and (fe-p (car poly))
           (field-polynomial-p (cdr poly)))
    (null poly)))

(defun polynomial-degree (poly)
  (if (endp poly) 0 (1- (len poly))))

(encapsulate
 (((poly-eval * *) => *)
  ((poly-sub * *) => *)
  ((poly-scale * *) => *)
  ((poly-derivative *) => *)
  ((square-free-polynomial-p *) => *)
  ((splits-polynomial-p *) => *)
  ((polynomial-root-list *) => *))

 (local (defun poly-eval (poly x) (declare (ignore poly x)) nil))
 (local (defun poly-sub (p q) (declare (ignore p q)) nil))
 (local (defun poly-scale (c p) (declare (ignore c p)) nil))
 (local (defun poly-derivative (p) (declare (ignore p)) nil))
 (local (defun square-free-polynomial-p (p) (declare (ignore p)) nil))
 (local (defun splits-polynomial-p (p) (declare (ignore p)) nil))
 (local (defun polynomial-root-list (p) (declare (ignore p)) nil))

 (defthm root-list-has-no-duplicates
   (implies (and (field-polynomial-p poly)
                 (square-free-polynomial-p poly)
                 (splits-polynomial-p poly))
            (no-duplicatesp-equal (polynomial-root-list poly))))

 (defthm member-of-root-list
   (implies (and (field-polynomial-p poly)
                 (square-free-polynomial-p poly)
                 (splits-polynomial-p poly))
            (iff (member-equal x (polynomial-root-list poly))
                 (and (fe-p x)
                      (equal (poly-eval poly x) (fzero))))))

 (defthm square-free-root-count
   (implies (and (field-polynomial-p poly)
                 (square-free-polynomial-p poly)
                 (splits-polynomial-p poly))
            (equal (len (polynomial-root-list poly))
                   (polynomial-degree poly)))))
