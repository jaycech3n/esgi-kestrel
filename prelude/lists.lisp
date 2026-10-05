(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/lists/top" :dir :system)

(defun nilp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (not xs)))

(defun true-consp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) xs))

(defun last-elem (xs) (first (last xs)))

; Logically, leaves non-conses untouched
(defun drop-vals (v xs)
  (declare (xargs :guard (true-listp xs)))
  (if (consp xs)
      (if (equal (first xs) v)
          (drop-vals v (rest xs))
          xs)
      xs))

(defun drop-vals-from-end (v xs)
  (declare (xargs :guard (true-listp xs)))
  (rev (drop-vals v (rev xs))))