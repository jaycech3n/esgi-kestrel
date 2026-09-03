; This just exists to import the required results about primes from the books

(ld "centaur/fty/package.lsp"           :dir :system)
(ld "projects/numbers/package.lsp"      :dir :system)
(ld "kestrel/prime-fields/package.lsp"  :dir :system)
(ld "kestrel/number-theory/package.lsp" :dir :system)

(include-book "kestrel/number-theory/top" :dir :system)

;; Theorems

(defthm prime-implies-integer
  (implies (dm::primep n) (integerp n)))