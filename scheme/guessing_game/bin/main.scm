#!/nix/store/77gw8l14kgwbix4x8giy9w3hpgyiis96-chez-scheme-racket-unstable-2021-12-11/bin/scheme --script
(import
  (chezscheme)
  (game-loop))
(game-loop (floor (random 100)) #t)
