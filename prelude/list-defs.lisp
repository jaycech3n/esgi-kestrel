(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/lists/top" :dir :system)

(defun nilp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (not xs)))

(defun true-consp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) xs))

(defun last-elem (xs) (first (last xs)))

(defun drop-vals (v xs)
  (cond ((atom xs) nil) ; treats all atoms as nil
        ((equal (first xs) v) (drop-vals v (rest xs)))
        (t xs)))

(defun drop-vals-from-end (v xs)
  (rev (drop-vals v (rev xs))))