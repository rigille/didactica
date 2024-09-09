(library (editor)
  (export
    event-loop make-editor-state editor-state-previous-lines
    editor-state-next-lines load-file)
  (import (rnrs records syntactic (6))
          (rnrs base (6))
          (rnrs io simple (6))
          (rnrs io ports (6))
          (rnrs control (6)))

  (define-record-type editor-state
    (fields
      (immutable previous-lines)
      (immutable next-lines)))

  (define (load-file filename)
    (call-with-input-file filename
      (lambda (port)
        (let loop ((previous '()))
          (let ((line (get-line port)))
            (if (eof-object? line)
                (make-editor-state '() (reverse previous))
                (loop (cons line previous))))))))

  (define (move-lines state n)
    (cond
      ((zero? n) state)
      ((positive? n)
       (let loop ((n n)
                  (prev (editor-state-previous-lines state))
                  (next (editor-state-next-lines state)))
         (if (or (zero? n) (null? next))
             (make-editor-state prev next)
             (loop (- n 1) (cons (car next) prev) (cdr next)))))
      (else ; negative n
       (let loop ((n n)
                  (prev (editor-state-previous-lines state))
                  (next (editor-state-next-lines state)))
         (if (or (zero? n) (null? prev))
             (make-editor-state prev next)
             (loop (+ n 1) (cdr prev) (cons (car prev) next)))))))

  (define (event-loop state filename)
    (display ":")
    (let ((input (get-line (current-input-port))))
      (cond
        ((string=? input "q") 'quit)
        ((string=? input "f") 
         (display "Filename: ")
         (event-loop state (get-line (current-input-port))))
        ((string=? input "r") 
         (event-loop (load-file filename) filename))
        ((string=? input "p")
         (unless (null? (editor-state-next-lines state))
           (display (car (editor-state-next-lines state)))
           (newline))
         (event-loop state filename))
        ((string->number input) =>
         (lambda (n) (event-loop (move-lines state n) filename)))
        (else 
         (display "Unknown command\n")
         (event-loop state filename))))))
