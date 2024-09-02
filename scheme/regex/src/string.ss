(define (concatenate . parameters)
  (let* ((total (fold-left
                  (lambda (total text)
                    (+ total (string-length text)))
                  0
                  parameters))
         (output (make-string total)))
    (fold-left
      (lambda (total text)
        (string-copy! text 0 output total (string-length text))
        (+ total (string-length text)))
      0
      parameters)
    output))
