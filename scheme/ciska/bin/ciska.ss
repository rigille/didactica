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
        (event-loop (make-editor-state 0 '() '()))
        (let ((filename (car fns)))
          (begin
            (display "loading ")
            (display filename)
            (display "...\n")
            (event-loop (load-file filename))))))))
