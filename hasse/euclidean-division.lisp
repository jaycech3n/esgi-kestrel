; Proof-carrying Euclidean division over F_p[X].

(in-package "ACL2")

(defun pf-poly-equal (x y p)
  (equal (pf-poly-normalize x p)
         (pf-poly-normalize y p)))

(defun pf-division-monic-polynomial-p (poly p)
  (let ((poly (pf-poly-normalize poly p)))
    (and (consp poly)
         (equal (car (last poly)) 1))))

(defun pf-remainder-degree-bounded-p (remainder divisor p)
  (let ((remainder (pf-poly-normalize remainder p))
        (divisor (pf-poly-normalize divisor p)))
    (and (consp divisor)
         (or (endp remainder)
             (< (len remainder) (len divisor))))))

(defun pf-divmod-certificate (quotient remainder)
  (list :pf-divmod quotient remainder))
(defun pf-divmod-quotient (certificate) (cadr certificate))
(defun pf-divmod-remainder (certificate) (caddr certificate))

(defun pf-divmod-certificate-p (dividend divisor p certificate)
  (let ((quotient (pf-divmod-quotient certificate))
        (remainder (pf-divmod-remainder certificate)))
    (and (equal (car certificate) :pf-divmod)
         (equal (len certificate) 3)
         (prime-number-p p)
         (pf-division-monic-polynomial-p divisor p)
         (pf-poly-equal
          dividend
          (pf-poly-add (pf-poly-mul quotient divisor p) remainder p)
          p)
         (pf-remainder-degree-bounded-p remainder divisor p))))

(defun normalize-polynomial-list (polys p)
  (if (endp polys)
      nil
    (cons (pf-poly-normalize (car polys) p)
          (normalize-polynomial-list (cdr polys) p))))

(defun polynomials-of-length-at-most (p length)
  (if (zp length)
      (list nil)
    (remove-duplicates-equal
     (append (polynomials-of-length-at-most p (1- length))
             (normalize-polynomial-list
              (coefficient-vectors p length) p)))))

(defun find-remainder-for-quotient
  (dividend divisor p quotient remainders)
  (if (endp remainders)
      nil
    (let ((certificate (pf-divmod-certificate quotient (car remainders))))
      (if (pf-divmod-certificate-p dividend divisor p certificate)
          certificate
        (find-remainder-for-quotient
         dividend divisor p quotient (cdr remainders))))))

(defun find-pf-divmod-certificate-aux
  (dividend divisor p quotients remainders)
  (if (endp quotients)
      nil
    (or (find-remainder-for-quotient
         dividend divisor p (car quotients) remainders)
        (find-pf-divmod-certificate-aux
         dividend divisor p (cdr quotients) remainders))))

(defun divmod-certificates-for-quotient (quotient remainders)
  (if (endp remainders)
      nil
    (cons (pf-divmod-certificate quotient (car remainders))
          (divmod-certificates-for-quotient quotient (cdr remainders)))))

(defun all-divmod-certificates (quotients remainders)
  (if (endp quotients)
      nil
    (append (divmod-certificates-for-quotient (car quotients) remainders)
            (all-divmod-certificates (cdr quotients) remainders))))

(defun find-valid-divmod-certificate (dividend divisor p certificates)
  (if (endp certificates)
      nil
    (if (pf-divmod-certificate-p dividend divisor p (car certificates))
        (car certificates)
      (find-valid-divmod-certificate
       dividend divisor p (cdr certificates)))))

(defun find-pf-divmod-certificate (dividend divisor p)
  (let* ((dividend (pf-poly-normalize dividend p))
         (divisor (pf-poly-normalize divisor p))
         (quotient-length
          (if (< (len dividend) (len divisor))
              1
            (1+ (- (len dividend) (len divisor)))))
         (remainder-length
          (if (endp divisor) 0 (1- (len divisor)))))
    (if (or (not (prime-number-p p))
            (not (pf-division-monic-polynomial-p divisor p)))
        nil
      (find-valid-divmod-certificate
       dividend divisor p
       (all-divmod-certificates
        (polynomials-of-length-at-most p quotient-length)
        (polynomials-of-length-at-most p remainder-length))))))

(defthm find-valid-divmod-certificate-is-valid
  (implies (find-valid-divmod-certificate
            dividend divisor p certificates)
           (pf-divmod-certificate-p
            dividend divisor p
            (find-valid-divmod-certificate
             dividend divisor p certificates)))
  :hints (("Goal"
           :induct (find-valid-divmod-certificate
                    dividend divisor p certificates)
           :expand ((find-valid-divmod-certificate
                     dividend divisor p certificates))
           :in-theory (disable pf-divmod-certificate-p))))

(defconst *pf-divmod-example*
  (find-pf-divmod-certificate '(1 0 0 0 1) '(1 1 1) 2))

(defthm pf-divmod-example-is-valid
  (pf-divmod-certificate-p '(1 0 0 0 1) '(1 1 1) 2
                           *pf-divmod-example*))
