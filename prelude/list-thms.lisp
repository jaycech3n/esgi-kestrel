(ld "lists.lisp")

(defthm drop-vals-of-append-last-ne
  (implies (not (equal x v))
           (consp (drop-vals v (append xs (list x)))))
  :hints (("Goal" :induct (len xs))))

(defthm consp-drop-vals-iff
  (implies (true-listp xs)
    (iff (consp (drop-vals v (rev xs)))
         (consp (drop-vals v xs)))))

(defthm drop-vals-all
  (implies (all-equalp v xs)
           (not (consp (drop-vals v xs)))) ; `not consp`, and not `nilp`!
  :hints (("Goal" :cases (true-listp xs))))

(defthm drop-vals-from-end-all
  (implies (all-equalp v xs)
           (nilp (drop-vals-from-end v xs))))