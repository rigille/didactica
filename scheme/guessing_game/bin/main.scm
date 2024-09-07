#! /usr/bin/env scheme-script

(import
  (chezscheme)
  (game-loop))
(game-loop (floor (random 100)) #t)
