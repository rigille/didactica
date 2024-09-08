{
  description = "Miscellaneous projects focused on good documentation and ease of understanding.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        chez = pkgs.chez;
      in
      {
        packages = {
          guessing-game = pkgs.stdenv.mkDerivation {
              name = "guessing-game";
              
              src = ./scheme;
              
              buildInputs = [ chez ];
              
              buildPhase = ''
                export CHEZSCHEMELIBDIRS=$(find . -type d -printf '%p:' | sed 's/:$//')
                ${chez}/bin/scheme -q <<EOF
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
                mkdir -p $out/bin $out/lib
                cp guessing-game.boot $out/lib
                echo '#!/bin/sh' > $out/bin/guessing-game
                echo '${chez}/bin/scheme --boot "'$out'/lib/guessing-game.boot" "$@"' >> $out/bin/guessing-game
                chmod +x $out/bin/guessing-game
              '';
            };
        };

        devShells = {
          default = pkgs.mkShell {
            # Development tools
            packages = [
              pkgs.gcc14
              pkgs.clang
              pkgs.chez
              pkgs.coq_8_17
              (pkgs.coqPackages_8_17.VST.overrideAttrs (final: previous: {
                src = pkgs.fetchFromGitHub {
                  owner = "PrincetonUniversity";
                  repo = "VST";
                  rev = "50a90d516380f86710450ef597fa3e40810bb59a";
                  sha256 = "sha256-/y9DtXIPQ9IetH5AEY/2oCQCRazTymU76MDnA9zpEyU=";
                };
              }))
              #pkgs.coqPackages.topology
            ];
            shellHook = ''
                export SYSTEM=${system}
                export CHEZSCHEMELIBDIRS=$(find $(pwd)/scheme -type d -printf '%p:' | sed 's/:$//')
            '';

            # Tools from packages
            inputsFrom = [
              #self.packages.${system}.guessing_game
            ];
          };
        };
      });
}
