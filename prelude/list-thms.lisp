(ld "lists.lisp")

(defthm singleton-len
  (implies (singletonp xs) (equal (len xs) 1)))

(defthm dropvals-consp-first
  (implies (consp (dropvals v xs))
           (not (equal (first (dropvals v xs)) v))))

(defthm dropvals-of-append-last-ne
  (implies (not (equal x v))
           (consp (dropvals v (append xs (list x)))))
  :hints (("Goal" :induct (len xs))))

(defthm consp-dropvals-of-rev-iff
  (implies (true-listp xs)
    (iff (consp (dropvals v (rev xs)))
         (consp (dropvals v xs)))))

(defthm dropvals-all
  (implies (all-equalp v xs)
           (not (consp (dropvals v xs)))) ; `not consp`, and not `nilp`!
  :hints (("Goal" :cases (true-listp xs))))

(defthm dropvals-from-end-all
  (implies (all-equalp v xs)
           (nilp (dropvals-from-end v xs))))