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
(defun drop-vals (v xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (first xs) v)
          (drop-vals v (rest xs))
          xs)
      xs))

(defun drop-vals-from-end (v xs)
  (rev (drop-vals v (rev xs))))

; Pads the front of the shorter list to the length of the longer
; (for now only used in the big endian representation of polynomials).
(defun pad-front-aux (a ls)
  (declare (xargs
    :guard (equal 2 (len ls))
    :measure (abs (- (len (first ls)) (len (second ls)))))
  )
  (if (equal 2 (len ls))
      (let ((xs (first ls))
            (ys (second ls)))
        (cond
          ((< (len xs) (len ys)) (pad-front-aux a (list (cons a xs) ys)))
          ((< (len ys) (len xs)) (pad-front-aux a (list xs (cons a ys))))
          (t (list xs ys))))
      :[pad-front-aux]-bad-inputs))

(defun pad-front (a xs ys) (pad-front-aux a (list xs ys)))
