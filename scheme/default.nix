{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  name = "guessing-game";
  
  src = ./.;
  
  buildInputs = [ pkgs.chez-racket ];
  
  buildPhase = ''
    export CHEZSCHEMELIBDIRS=$(find . -type d -printf '%p:' | sed 's/:$//')
    ${pkgs.chez-racket}/bin/scheme -q <<EOF
    (import (chezscheme))
    (optimize-level 2)
    (generate-wpo-files #t)
    (compile-imported-libraries #t)
    (compile-program "guessing-game/bin/guessing-game.scm")
    (compile-whole-program "guessing-game/bin/guessing-game.wpo" "guessing-game.so"))
    (make-boot-file "guessing-game.boot" '("scheme" "petite") "guessing-game.so")
    (exit)
    EOF
  '';

  installPhase = ''
    mkdir -p $out/bin $out/lib/
    cp guessing-game.boot $out/lib/
    ln -s ${pkgs.chez-racket}/bin/scheme $out/bin/guessing-game
  '';
}
