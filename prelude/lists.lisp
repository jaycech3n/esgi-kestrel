(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/lists/top" :dir :system)

(defun nilp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (not (consp xs))))

(defun true-consp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (consp xs)))

(defun singleton (xs)
  (declare (xargs :guard t))
  (and (true-consp xs) (nilp (rest xs))))

(defun last-elem (xs) (first (last xs)))

; Logically, leaves non-conses untouched
(defun drop-vals (v xs)
  (if (consp xs)
      (if (equal (first xs) v)
          (drop-vals v (rest xs))
          xs)
      xs))

(defun drop-vals-from-end (v xs)
  (rev (drop-vals v (rev xs))))