(library (editor)
  (export
    event-loop)
  (import
    (rnrs records syntactic (6))
    (rnrs base (6))
    (rnrs io simple (6))
    (rnrs io ports (6))
    (rnrs control (6))
    (rnrs eval (6))
    (ciska-commands))

  (define (event-loop state)
    (display ":")
    (let ((command (get-datum (current-input-port))))
      (event-loop ((eval command (environment '(rnrs) '(ciska-commands) '(chezscheme))) state)))))
