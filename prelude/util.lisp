(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(defmacro section (&rest content)
  (cons 'encapsulate (cons 'nil content)))

; (defmacro section-enable (names &rest content)
;   (cons 'section
;     (cons (list 'local (list 'in-theory (cons 'enable names)))
;           content)))

; (defmacro section-disable (names &rest content)
;   (cons 'section
;     (cons (list 'local (list 'in-theory (cons 'disable names)))
;           content)))

; (defmacro section-e/d (enames dnames &rest content)
;   (cons 'section
;     (cons (list 'local (list 'in-theory (list 'e/d enames dnames)))
;           content)))

(defconst *std-imports*
  (union-eq '(acl2::define
              acl2::defrule
              acl2::defruled
              acl2::section)
            *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))