; Arbitrary-degree irreducibility verification and exhaustive construction
; over prime fields.  This is intentionally a simple reference algorithm.

(in-package "ACL2")

(defun append-monic-leading-one (coefficient-vectors)
  (if (endp coefficient-vectors)
      nil
    (cons (append (car coefficient-vectors) '(1))
          (append-monic-leading-one (cdr coefficient-vectors)))))

(defun monic-polynomials-of-degree (p degree)
  (if (zp degree)
      (list '(1))
    (append-monic-leading-one (coefficient-vectors p degree))))

(defun monic-polynomials-through-degree (p degree)
  (if (zp degree)
      nil
    (append (monic-polynomials-through-degree p (1- degree))
            (monic-polynomials-of-degree p degree))))

(defun pf-zero-polynomial-p (poly p)
  (endp (pf-poly-normalize poly p)))

(defun pf-poly-divides-p (divisor poly p)
  (and (not (pf-zero-polynomial-p divisor p))
       (pf-zero-polynomial-p (pf-poly-mod poly divisor p) p)))

(defun some-polynomial-divides-p (divisors poly p)
  (if (endp divisors)
      nil
    (or (pf-poly-divides-p (car divisors) poly p)
        (some-polynomial-divides-p (cdr divisors) poly p))))

(defun pf-monic-polynomial-p (poly p)
  (let ((poly (pf-poly-normalize poly p)))
    (and (consp poly)
         (equal (car (last poly)) 1))))

(defun pf-irreducible-by-trial-p (poly p)
  (let* ((poly (pf-poly-normalize poly p))
         (degree (pf-poly-degree poly)))
    (and (prime-number-p p)
         (pf-monic-polynomial-p poly p)
         (posp degree)
         (not (some-polynomial-divides-p
               (monic-polynomials-through-degree p (floor degree 2))
               poly p)))))

(defun find-first-irreducible (candidates p)
  (if (endp candidates)
      nil
    (if (pf-irreducible-by-trial-p (car candidates) p)
        (car candidates)
      (find-first-irreducible (cdr candidates) p))))

(defun find-irreducible-polynomial (p degree)
  (if (or (not (prime-number-p p)) (not (posp degree)))
      nil
    (find-first-irreducible
     (monic-polynomials-of-degree p degree) p)))

(defthm find-first-irreducible-is-irreducible
  (implies (find-first-irreducible candidates p)
           (pf-irreducible-by-trial-p
            (find-first-irreducible candidates p) p))
  :hints (("Goal"
           :induct (find-first-irreducible candidates p)
           :expand ((find-first-irreducible candidates p))
           :in-theory (disable pf-irreducible-by-trial-p))))

(defthm find-irreducible-polynomial-is-irreducible
  (implies (find-irreducible-polynomial p degree)
           (pf-irreducible-by-trial-p
            (find-irreducible-polynomial p degree) p))
  :hints (("Goal"
           :cases ((and (prime-number-p p) (posp degree)))
           :use ((:instance find-first-irreducible-is-irreducible
                            (candidates
                             (monic-polynomials-of-degree p degree))))
           :in-theory (e/d (find-irreducible-polynomial)
                           (pf-irreducible-by-trial-p
                            prime-number-p
                            find-first-irreducible-is-irreducible)))))

(defun ff-general-field-p (field)
  (let ((p (ff-characteristic field)))
    (and (prime-number-p p)
         (or (and (equal (ff-kind field) :prime)
                  (equal (len field) 2))
             (and (equal (ff-kind field) :extension)
                  (equal (len field) 3)
                  (pf-irreducible-by-trial-p (ff-modulus field) p))))))

(defun construct-extension-field (p degree)
  (let ((modulus (find-irreducible-polynomial p degree)))
    (if modulus
        (list :extension p modulus)
      nil)))

(defthm constructed-extension-has-verified-modulus
  (implies (construct-extension-field p degree)
           (pf-irreducible-by-trial-p
            (ff-modulus (construct-extension-field p degree)) p))
  :hints (("Goal"
           :use ((:instance find-irreducible-polynomial-is-irreducible))
           :in-theory (e/d (construct-extension-field ff-modulus)
                           (pf-irreducible-by-trial-p
                            find-irreducible-polynomial-is-irreducible)))))

; Executable regression witnesses beyond the old degree-at-most-three checker.
(defconst *ff16-modulus* (find-irreducible-polynomial 2 4))
(defconst *ff16* (construct-extension-field 2 4))

(defthm ff16-modulus-is-irreducible
  (pf-irreducible-by-trial-p *ff16-modulus* 2))

(defthm ff16-is-a-general-field
  (ff-general-field-p *ff16*))

(defthm ff16-has-sixteen-enumerated-elements
  (equal (len (ff-elements *ff16*)) 16))
