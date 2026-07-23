;; Natural numbers

(defun succ (n) (declare (type (satisfies natp) n)) (+ n 1))
(defun pred (n) (declare (type (satisfies natp) n)) (- n 1))

;; Logic

(defthmd iff-intro (equal (iff P Q) (and (implies P Q) (implies Q P))))

;; Lists

(defun dropVals (v l)
  (if (endp l) l
      (if (equal (car l) v)
          (dropVals v (cdr l))
          l)))

(defun dropValsFromEnd (v l)
  (reverse (dropVals v (reverse l))))

; Ranges and some lemmas

(defun range-aux (n l)
  (declare (type (satisfies natp) n))
  (if (zp n) l (range-aux (pred n) (cons (pred n) l))))

(defun range (n)
  (declare (type (satisfies natp) n))
  (range-aux n nil))

(defun in-rangep (n x)
  (and (<= 0 x) (< x n)))

; Prove this at some point.
(defaxiom in-rangep-2-vals (implies (in-rangep 2 x) (or (= x 0) (= x 1))))
