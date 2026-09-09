;; Imports

(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/lists/top" :dir :system)

;; Numbers

(defun nat-succ (n) (1+ n))
(defun nat-pred (n) (if (zp n) 0 (1- n)))

(defthm nat-pred-nonnat
  (implies (not (natp n)) (equal (nat-pred n) 0)))

;; Lists

; Enable/disable definitions to adjust
; high-level/low-level reasoning in proofs.
(in-theory (disable all-equalp))
(in-theory (enable repeat))

(defun true-consp (xs) (and (true-listp xs) (consp xs)))

(defun last-elem (xs) (first (last xs)))

(defun map- (xs)
  (if (consp xs)
      (cons (- (first xs)) (map- (rest xs)))
      xs))

; This treats true and non-true consp lists the same
(defun drop-vals (v xs)
  (cond ((atom xs) nil)
        ((equal v (first xs)) (drop-vals v (rest xs)))
        (t xs)))

(defun drop-vals-from-end (v xs)
  (rev (drop-vals v (rev xs))))

; Some theorems

(defthm rev-all-equal
  (iff (all-equalp v (rev xs))
       (all-equalp v xs)))

(defthm intlist-rev
  (implies (not (integer-listp (rev xs)))
           (not (integer-listp xs))))

(defthm intlist-drop-vals
  (implies (not (integer-listp (drop-vals v xs)))
           (not (integer-listp xs))))

(defthm rev-intlist-closed
  (implies (true-listp xs)
    (iff (integer-listp (rev xs))
         (integer-listp xs))))

(defthm drop-vals-intlist-closed
  (implies (integer-listp xs)
           (integer-listp (drop-vals v xs))))

(defthm drop-vals-from-end-intlist-closed
  (implies (integer-listp xs)
           (integer-listp (drop-vals-from-end v xs))))

(defthm drop-vals-last-ne-val
  (implies (not (equal v x))
           (consp (drop-vals v (append xs (list x)))))
  :hints (("Goal" :induct (len xs))))

(defthm consp-drop-vals-append
  (implies (consp (drop-vals v xs))
           (consp (drop-vals v (append xs ys)))))

(defthm drop-vals-all
  (implies (all-equalp v xs)
           (not (drop-vals v xs))))

(defthm drop-vals-from-end-all
  (implies (all-equalp v xs)
           (not (drop-vals-from-end v xs))))

(defthm intlist-append
  (implies (and (integer-listp xs)
                (integer-listp (append xs ys)))
           (integer-listp ys)))

(defthm append-intlist-closed
  (implies (and (integer-listp xs) (integer-listp ys))
           (integer-listp (append xs ys))))

(defthm intlist-repeat
  (implies (and (natp n) (integerp x)) (integer-listp (repeat n x))))