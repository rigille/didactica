(library (ciska-commands)
  (export
    make-editor-state editor-state-previous-lines
    editor-state-next-lines move-lines load-file
    show go show-range)
  #;(import
    (rnrs records syntactic (6))
    (rnrs records procedural)
    (rnrs base (6))
    (rnrs io simple (6))
    (rnrs io ports (6))
    (rnrs control (6))
    (rnrs syntax-case))
  (import (chezscheme))

  (define-syntax update-record
    (syntax-rules ()
      ((_ original ((field value) ...))
       (let* ((rtd (record-rtd original))
              (field-count (vector-length (record-type-field-names rtd)))
              (constructor (record-constructor
                             (make-record-constructor-descriptor
                               rtd #f (lambda (p) p)))))
         (apply constructor
           (let loop ((i 0))
             (if (= i field-count)
                 '()
                 (cons
                   (let ((name (vector-ref (record-type-field-names rtd) i)))
                     (cond
                       ((assq name '((field value) ...)) => cadr)
                       (else ((record-accessor rtd i) original))))
                   (loop (+ i 1))))))))))

  (define (compose f g)
    (lambda (x)
      (f (g x))))

  (define (chain . fns)
    (let loop ((fns fns)
               (chained (lambda (x) x)))
      (if (null? fns)
          chained
          (loop (cdr fns) (compose (car fns) chained)))))

  (define-record-type editor-state
    (fields
      (immutable position)       ; should equal length of previous lines
      (immutable previous-lines)
      (immutable next-lines)))

  (define (load-file filename)
    (call-with-input-file filename
      (lambda (port)
        (let loop ((previous '()))
          (let ((line (get-line port)))
            (if (eof-object? line)
                (make-editor-state 0 '() (reverse previous))
                (loop (cons line previous))))))))

  (define (move-lines n)
    (lambda (state)
      (cond
        ((zero? n) state)
        ((positive? n)
         (let loop ((n n)
                    (prev (editor-state-previous-lines state))
                    (next (editor-state-next-lines state)))
           (if (or (zero? n) (null? next))
               (make-editor-state (+ (editor-state-position state) n) prev next)
               (loop (- n 1) (cons (car next) prev) (cdr next)))))
        (else ; negative n
         (let loop ((n n)
                    (prev (editor-state-previous-lines state))
                    (next (editor-state-next-lines state)))
           (if (or (zero? n) (null? prev))
               (make-editor-state (+ (editor-state-position state) n) prev next)
               (loop (+ n 1) (cdr prev) (cons (car prev) next))))))))

  (define (go n)
    (lambda (state)
      ((move-lines (- n (editor-state-position state))) state)))

  (define (show n)
    (lambda (state)
      (let ((lines (editor-state-next-lines state)))
        (let loop ((i 0)
                   (lines lines))
          (if
            (or (>= i n) (null? lines))
            state
            (begin
              (display (car lines))
              (display #\newline)
              (loop (+ i 1) (cdr lines))))))))

  (define (show-range a b)
    (chain
      (go a)
      (show (- b a)))))
