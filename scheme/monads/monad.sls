(import (day01 solution))

(define-record-type monad (fields (immutable bind) (immutable pure)))

(define-syntax let-bind*
  (syntax-rules ()
    ((_ m () b1 b2 ...)
     ((monad-pure m) (begin b1 b2 ...)))
    ((_ m ((i1 e1) (i2 e2) ...) b1 b2 ...)
     ((monad-bind m) e1 (lambda (i1)
       (let-bind* m ([i2 e2] ...) b1 b2 ...))))))

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

(define (sequence . parsers) (if (null? parsers)
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
    (fold-left (lambda (acc d) (+ (* 10 acc) d)) 0 digits)))

(define example-game
  "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green")

(define-record-type ball (fields number color))

(define parse-ball
  (let-bind* parser
    ((l (sequence (literal " ")
		  number
		  (literal " ")
                  (choice (literal "blue" 'blue)
                          (literal "red" 'red)
                          (literal "green" 'green)))))
    (make-ball (car l) (cadr l))))
(define (separated
	  value separator)
  (let-bind* parser
    ((h value)
     (t (many (sequence
		separator
		value))))
    (cons h (map car t))))

(define-record-type game (fields id entries))

(define parse-game
  (let ((game-header (sequence
		       (literal "Game ")
		       number
		       (literal ":")))
	(balls (separated
		 parse-ball
	         (choice (literal ",")
		         (literal ";")))))
    (let-bind* parser
      ((game-id game-header)
       (entries balls))
      (make-game (car game-id) entries))))
 #|(part1 game-instance
  (if (for-all
	    (lambda (r)
	      (>= (case (ball-color r)
		    ('blue 14)
		    ('green 13)
		    ('red 12))
		  (ball-number r)))
	    entries)
          game-id
	  0)|#

#; (display
  (let loop ((file (open-input-file "input.txt"))
	     (sum 0))
    (let ((line (get-line file)))
      (case line
	(#!eof sum)
	(else (loop file (+ sum (run parse-game line))))))))

(define (feasible l color)
  (apply max
    (map (lambda (r)
	   (ball-number r))
      (filter
        (lambda (r)
	  (eq? (ball-color r)
	       color))
        l))))
(define (power game)
  (let ((entries (game-entries game)))
    (* (feasible entries 'blue)
       (feasible entries 'red)
       (feasible entries 'green))))

(display
  (let loop ((file (open-input-file "input.txt"))
	     (sum 0))
    (let ((line (get-line file)))
      (case line
	(#!eof sum)
	(else (loop file (+ sum (power (run parse-game line)))))))))
