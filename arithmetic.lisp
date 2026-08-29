(include-book "arithmetic/top-with-meta" :dir :system)

(defun mod+ (n x y) (mod (+ (ifix x) (ifix y)) (ifix n)))
(defun mod* (n x y) (mod (* (ifix x) (ifix y)) (ifix n)))
(defun mod- (n x y) (mod (- (ifix x) (ifix y)) (ifix n)))