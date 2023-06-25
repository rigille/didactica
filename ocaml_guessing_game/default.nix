{ pkgs }:
let
  ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
in
pkgs.stdenv.mkDerivation {
  name = "guessing_game";
  src = ./.;
  buildInputs = [
    ocamlPackages.ocaml
    ocamlPackages.dune_3
  ];
  buildPhase = ''
  dune build -p guessing_game
  '';
  installPhase = ''
  dune install --prefix=$out
  '';
}
