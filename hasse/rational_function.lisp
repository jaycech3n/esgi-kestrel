(defun finite-field-polynomial-p (poly)
  (if (consp poly)
      (and (ffieldp (car poly))
           (finite-field-polynomial-p (cdr poly)))
      (null poly)))


(member '1 '(2 3 1))

(member '1 '(2 5 3))
