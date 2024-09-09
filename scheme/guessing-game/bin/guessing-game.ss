(import
  (chezscheme)
  (game-loop))
(suppress-greeting #t)
(scheme-start
  (lambda fns
    (game-loop (floor (random 100)) #t)))
