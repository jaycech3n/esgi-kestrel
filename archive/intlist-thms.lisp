(ld "intlist-defuns.lisp")

; --- rev ---

(defthm intlist-rev
  (implies (not (integer-listp (rev xs)))
           (not (integer-listp xs)))
  :hints (("Goal" :in-theory (enable rev)
                  :induct (len xs))))

(defthm rev-intlist-closed
  (implies (true-listp xs)
    (iff (integer-listp (rev xs))
         (integer-listp xs))))

; --- drop-vals ---

(defthm intlist-drop-vals
  (implies (not (integer-listp (drop-vals v xs)))
           (not (integer-listp xs))))

(defthm drop-vals-intlist-closed
  (implies (integer-listp xs)
           (integer-listp (drop-vals v xs))))

(defthm drop-vals-from-end-intlist-closed
  (implies (integer-listp xs)
           (integer-listp (drop-vals-from-end v xs))))

; --- append ---

(defthm intlist-append
  (implies (and (integer-listp xs)
                (integer-listp (append xs ys)))
           (integer-listp ys)))

(defthm append-intlist-closed
  (implies (and (integer-listp xs) (integer-listp ys))
           (integer-listp (append xs ys)))
  :rule-classes :type-prescription)

; --- repeat ---

(defthm intlist-repeat
  (implies (and (natp n) (integerp x)) (integer-listp (repeat n x)))
  :rule-classes :type-prescription)