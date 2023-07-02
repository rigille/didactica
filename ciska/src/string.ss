(define (concatenate first second)
  (let ((output (make-string (+ (string-length first) (string-length second)))))
    (string-copy! first 0 output 0 (string-length first))
    (string-copy! second 0 output (string-length first) (string-length second))
    output))
(define (cat . parameters)
    (let ((total (fold-left
                   (lambda (total text)
                     (+ total (string-length text)))
                   0
                   parameters)))
      (make-string total)))
