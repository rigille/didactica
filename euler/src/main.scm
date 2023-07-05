(import
  (chezscheme)
  (game-loop))
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
(game-loop (floor (random 100)) #t)
