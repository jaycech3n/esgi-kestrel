;; Numbers

(defun nat-succ (n)
  (declare (type (satisfies natp) n))
  (+ n 1))

(defun nat-pred (n)
  (declare (type (satisfies natp) n))
  (if (zp n) 0 (- n 1)))

;; Lists

(defun drop-vals (v xs)
  (if (endp xs)
      xs
      (if (equal v (first xs))
          (drop-vals v (rest xs))
          xs)))

(defun drop-vals-from-end (v xs)
  (reverse (drop-vals v (reverse xs))))

; Various list lemmas and functions

(defun zip+ (xs ys)
  (declare (type (satisfies integer-listp) xs ys))
  (if (endp xs)
      ys
      (if (endp ys)
          xs
          (cons (+ (first xs) (first ys)) (zip+ (rest xs) (rest ys))))))

(defun map- (xs)
  (declare (type (satisfies integer-listp) xs))
  (if (endp xs)
      xs
      (cons (- (first xs)) (map- (rest xs)))))

(defun mapmod (n xs)
  (declare (type (satisfies integer-listp) xs))
  (declare (type (satisfies integerp) n))
  (declare (xargs :guard (not (zerop n))))
  (if (endp xs)
      xs
      (cons (mod (car xs) n) (mapmod n (rest xs)))))
