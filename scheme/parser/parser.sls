(library (monadic-parser)
  (export
    make-parser-success parser literal run many sequence choice maybe)
  (import (monads))
  (define-record-type parser-success (fields value cursor))

  (define (bind parser next)
    (lambda (text cursor)
      (let ((reply (parser text cursor)))
        (if (parser-success? reply)
            ((next (parser-success-value reply)) text (parser-success-cursor reply))
            #f))))

  (define (pure value)
    (lambda (text cursor)
      (make-parser-success value cursor)))

  (define parser (make-monad bind pure))

  (define (literal entry . value)
      (lambda (text cursor)
        (if (substring? text cursor entry 0)
            (make-parser-success
              (if (null? value)
                  'ignore
                  (car value))
              (+ cursor (string-length entry)))
            #f)))

  (define digit
      (lambda (text cursor)
        (if (and (< cursor (string-length text))
                 (digit? (string-ref text cursor)))
            (make-parser-success
              (char- (string-ref text cursor) #\0)
              (+ cursor 1))
            #f)))

  (define (run parser text)
    (let ((reply (parser text 0)))
      (if (parser-success? reply)
        (parser-success-value (parser text 0))
        #f)))

  (define (many parser)
    (lambda (text cursor)
      (let ((reply (parser text cursor)))
        (if (parser-success? reply)
            (let ((tail ((many parser) text (parser-success-cursor reply))))
              (make-parser-success
                (cons (parser-success-value reply) (parser-success-value tail))
                (parser-success-cursor tail)))
            (make-parser-success (list) cursor)))))

  (define (sequence . parsers)
    (if (null? parsers)
        (pure (list))
        (let-bind* parser ((h (car parsers))
                           (t (apply sequence (cdr parsers))))
          (if (eq? h 'ignore)
              t
              (cons h t)))))

  (define (many1 parser)
    (sequence (list parser (many parser))))

  (define (choice . parsers)
    (lambda (text cursor)
      (if (null? parsers)
          #f
          (let ((reply ((car parsers) text cursor)))
            (if (parser-success? reply)
                reply
                ((apply choice (cdr parsers)) text cursor))))))

  (define (maybe parser)
    (lambda (text cursor)
      (let ((reply (parser text cursor)))
        (if (parser-success? reply)
            reply
            (make-parser-success 'ignore text cursor)))))

  (define number
    (let-bind* parser
      ((digits (many digit)))
      (fold-left (lambda (acc d) (+ (* 10 acc) d)) 0 digits))))
