(import
  (chezscheme)
  (number-theory))
(define (euler-1)
    (letrec ((loop (lambda (n limit total)
             (if (>= n limit)
               total
               (loop
                 (+ n 1)
                 limit
                 (+
                   total
                   (if
                     (or
                       (= (mod n 3) 0)
                       (= (mod n 5) 0))
                     n
                     0)))))))
      (loop 1 1000 0)))
(define (euler-5)
    (letrec ((range-multiple (lambda (n)
                               (if (= n 1)
                                 1
                                 (let ((previous (range-multip
le (- n 1))))
                                   (/ (* n previous)
                                      (greatest-common-divisor
 n previous)))))))
      (range-multiple 20)))
