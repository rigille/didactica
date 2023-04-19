{ pkgs }:
let
  ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
in
pkgs.stdenv.mkDerivation {
  name = "guessing-game";
  src = ./.;
  buildInputs = [
    ocamlPackages.ocaml
    ocamlPackages.dune_3
  ];
  buildPase = ''
  dune build -p guessing_game
  '';
  installPhase = ''
  dune install --prefix=$out
  '';
}
