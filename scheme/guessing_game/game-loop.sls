(library (game-loop)
  (export game-loop)
  (import (chezscheme))

  (define (game-loop secret-number first)
    (if first
      (display-string "What's your guess?\n")
      (display-string "Try again. What's your next guess?\n"))
    (display-string "> ")
    (let ((guess (read)))
      (if (number? guess)
        (cond
          ((< guess secret-number)
            (display-string "Too small!\n")
            (game-loop secret-number #f))
          ((> guess secret-number)
            (display-string "Too big!\n")
            (game-loop secret-number #f))
          ((= guess secret-number)
            (display-string "You won, congratulations!\n")))
        (begin
          (display-string "This doesn't seem to be a number. Could you try again?\n")
          (game-loop secret-number #f))))))
