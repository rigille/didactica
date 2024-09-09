(import
  (chezscheme)
  (editor))
(suppress-greeting #t)
(scheme-start
  (lambda fns
    (if (null? fns)
      (event-loop (make-editor-state '() '()) "")
      (let ((filename (car fns)))
          (event-loop (load-file filename) filename)))))
