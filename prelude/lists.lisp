(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/lists/top" :dir :system)

(defun nilp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (atom xs)))

(defun true-consp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (consp xs)))

(defun singletonp (xs)
  (declare (xargs :guard t))
  (and (consp xs) (nilp (rest xs))))

(defun pairp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs) (equal (len xs) 2)))

(defun last-elem (xs) (first (last xs)))

; Logically, leaves non-conses untouched
(defun dropvals (v xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (first xs) v)
          (dropvals v (rest xs))
          xs)
      xs))

(defun dropvals-from-end (v xs)
  (rev (dropvals v (rev xs))))
