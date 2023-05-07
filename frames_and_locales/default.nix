{ pkgs ? import <nixpkgs> {} }:
let
  coqPackages = pkgs.coqPackages;
in
pkgs.stdenv.mkDerivation {
  name = "guessing_game";
  src = ./.;
  buildInputs = [
    pkgs.coq
    coqPackages.coqide
    (import ../nix/topology.nix {pkgs=pkgs;})
  ];
  buildPhase = ''
  '';
  installPhase = ''
  '';
}
