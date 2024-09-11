(import
  (chezscheme)
  (ciska-commands)
  (editor))
(suppress-greeting #t)
(scheme-start
  (lambda fns
    (let-values (((first second third)
              ((library-search-handler) 'loader '(ciska-commands) (library-directories) (library-extensions))))
      (if second
        (load second)
        (load first))
      (if (null? fns)
        (event-loop (make-editor-state '() '()))
        (let ((filename (car fns)))
            (event-loop (load-file filename)))))))
