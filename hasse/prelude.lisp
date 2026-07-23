;; Natural numbers

(defun succ (n) (declare (type (satisfies natp) n)) (+ n 1))
(defun pred (n) (declare (type (satisfies natp) n)) (- n 1))

; A natural number "range" is a half-open interval.
(defun in-rangep (a b x)
  (declare (type (satisfies natp) a b x))
  (and (<= a x) (< x b)))

; "x is a natural in the range [0, n)"
(defun finp (n x)
  (declare (type (satisfies natp) n))
  (and (natp x) (in-rangep 0 n x)))


;; Lists

(defun dropVals (v l)
  (if (endp l) l
      (if (equal (car l) v)
          (dropVals v (cdr l))
          l)))

(defun dropValsFromEnd (v l)
  (reverse (dropVals v (reverse l))))
