(defstub wrap (xs) t)
(defstub plus (xs ys) t)

(defaxiom runit
  (implies xs
           (equal (plus xs (list 0)) xs)))

(defthm test
  (implies (consp xs)
           (wrap (plus xs (list 0))))
  :hints (("Goal" :do-not-induct t)))