(library (monads)
  (export monad make-monad monad-bind monad-pure let-bind*)

  (define-record-type
    monad
    (fields (immutable bind) (immutable pure)))

  (define-syntax let-bind*
    (syntax-rules ()
      ((_ m () b1 b2 ...)
       ((monad-pure m) (begin b1 b2 ...)))
      ((_ m ((i1 e1) (i2 e2) ...) b1 b2 ...)
       ((monad-bind m) e1 (lambda (i1)
         (let-bind* m ([i2 e2] ...) b1 b2 ...)))))))
