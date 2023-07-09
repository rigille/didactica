(library (regex)
  (export regex? regex-constructor?
          make-regex-concatenate regex-concatenate? regex-concatenate-left
          regex-concatenate-right
          make-regex-union regex-union? regex-union-left regex-union-right
          regex-star regex-star? regex-star-subject)
  (import (rnrs))
  ; records to compose regexes
  (define-record-type regex-concatenate (fields left right))
  (define-record-type regex-union (fields left right))
  (define-record-type regex-star (fields subject))
  ; regexes can also be characters, 'empty-set or 'empty-string
  (define (regex-constructor? candidate)
    (or
      (eqv? 'empty-set candidate)
      (eqv? 'empty-string candidate)
      (char? candidate)
      (regex-concatenate? candidate)
      (regex-union? candidate)
      (regex-star? candidate)))
  (define (regex? candidate)
    (cond
      ((eqv? 'empty-set candidate) #t)
      ((eqv? 'empty-string candidate) #t)
      ((char? candidate) #t)
      ((regex-concatenate? candidate)
         (and
           (regex? (regex-concatenate-left candidate))
           (regex? (regex-concatenate-right candidate))))
      ((regex-union? candidate)
         (and
           (regex? (regex-union-left candidate))
           (regex? (regex-union-right candidate))))
      ((regex-star? candidate)
         (regex? (regex-star-subject candidate)))
      (else #f))))


