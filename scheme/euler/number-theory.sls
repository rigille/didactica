(library (number-theory)
  (export greatest-common-divisor)
  (import (chezscheme))

  (define (greatest-common-divisor n m)
    (letrec ((loop (lambda (n m)
		     (if (= m 0)
		       n
		       (loop m (mod n m))))))
      (loop (max n m) (min n m)))))
