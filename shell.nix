{ pkgs ? import <nixpkgs> {} }:
let
  ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
in
pkgs.mkShell {
  name = "didactica";
  buildInputs = [
    ocamlPackages.ocaml
    ocamlPackages.dune_3
    ocamlPackages.odoc
    ocamlPackages.utop
    ocamlPackages.ocaml-lsp
    pkgs.ocamlformat
    pkgs.tree
  ];
  shellHook = (builtins.readFile ./.bashrc);
}
