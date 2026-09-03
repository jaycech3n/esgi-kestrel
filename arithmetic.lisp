(include-book "arithmetic/top-with-meta" :dir :system)

(defun mod+ (n x y)
  (if (zp n)
      :error[mod+][mod-by-zero]
      (mod (+ (ifix x) (ifix y)) (ifix n))))

(defun mod* (n x y)
  (if (zp n)
      :error[mod*][mod-by-zero]
      (mod (* (ifix x) (ifix y)) (ifix n))))

(defun mod- (n x y)
  (if (zp n)
      :error[mod-][mod-by-zero]
      (mod (- (ifix x) (ifix y)) (ifix n))))
