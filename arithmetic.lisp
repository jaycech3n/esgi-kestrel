(include-book "arithmetic-5/top" :dir :system)
; (include-book "arithmetic/top-with-meta" :dir :system)

(ld "prelude.lisp")

(defun mod+ (x y n)
  (let ((k (ifix n)))
    (if (zp k)
      :error[mod+][mod-by-zero]
      (mod (+ (ifix x) (ifix y)) k))))

(defun mod* (x y n)
  (let ((k (ifix n)))
    (if (zp k)
      :error[mod*][mod-by-zero]
      (mod (* (ifix x) (ifix y)) k))))

(defun mod- (x y n)
  (let ((k (ifix n)))
    (if (zp k)
      :error[mod-][mod-by-zero]
      (mod (- (ifix x) (ifix y)) k))))

(defun mapmod (xs n)
  (if (consp xs)
      (cons (mod (first xs) n) (mapmod (rest xs) n))
      xs))


;; Theorems

(defthm mod-idem
  (equal (mod (mod x n) n) (mod x n)))

(defthm mod+-mod-snd
  (equal (mod+ x (mod y n) n) (mod+ x y n)))

(defthm mapmod-integer-closed
  (implies (and (integerp n)
                (integer-listp xs))
           (integer-listp (mapmod xs n))))

(defthm mapmod-idem
  (equal (mapmod (mapmod xs n) n) (mapmod xs n)))