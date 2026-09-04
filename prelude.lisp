;; Imports

(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/lists/append-theorems" :dir :system)

;; Numbers

(defun nat-succ (n) (1+ n))
(defun nat-pred (n) (if (zp n) 0 (1- n)))

(defthm nat-pred-nonnat
  (implies (not (natp n)) (equal (nat-pred n) 0)))

;; Lists

(defun nilp (xs) (equal nil xs))
(defun true-consp (xs) (and (true-listp xs) (consp xs)))

; Because the std book's all-equalp is annoying.
(defun all-equalp-nofix (v xs)
  (if (true-listp xs)
      (if (endp xs)
          t
          (and (equal v (first xs)) (all-equalp-nofix v (rest xs))))
      nil))

(defun last-elem (xs) (first (last xs)))

(defun map- (xs)
  (if (consp xs)
      (cons (- (first xs)) (map- (rest xs)))
      xs))

(defun mapmod (n xs)
  (if (consp xs)
      (cons (mod (first xs) n) (mapmod n (rest xs)))
      xs))

(defun drop-vals (v xs)
  (if (consp xs)
      (if (equal v (first xs))
          (drop-vals v (rest xs))
          xs)
      xs))

(defun drop-vals-from-end (v xs)
  (reverse (drop-vals v (reverse xs))))

; Some theorems

(defthm mapmod-closed
  (implies (and (integerp n)
                (integer-listp xs))
           (integer-listp (mapmod n xs))))

(defthm drop-vals-last-ne-val
  (implies (not (equal v x))
           (consp (drop-vals v (append xs (list x)))))
  :hints (("Goal" :induct (len xs))))

(defthm consp-drop-vals-append
  (implies (consp (drop-vals v xs))
           (consp (drop-vals v (append xs ys)))))


