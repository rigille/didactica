(define (concatenate first second)
  (let ((output (make-string (+ (string-length first) (string-length second)))))
    (string-copy! first 0 output 0 (string-length first))
    (string-copy! second 0 output (string-length first) (string-length second))
    output))
(define (cat . parameters)
      (let* ((total (fold-left
                     +
                     0                                                       (map string-length parameters)))
             (fresh (make-string total)))
        fresh))
