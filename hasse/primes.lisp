;; This just exists to import the required results about primes from the books

(in-package "HASSE-THM")

(ld "centaur/fty/package.lsp"           :dir :system)
(ld "projects/numbers/package.lsp"      :dir :system)
(ld "kestrel/prime-fields/package.lsp"  :dir :system)
(ld "kestrel/number-theory/package.lsp" :dir :system)

(include-book "kestrel/number-theory/top" :dir :system)
