{ pkgs ? import <nixpkgs> {} }:
(pkgs.coqPackages.mkCoqDerivation rec {
  pname = "topology";
  releaseRev = "f784257d0b9c316601440e4f02256bd6068e4f94";
  src = pkgs.fetchFromGitHub {
    owner = "coq-community";
    repo = "topology";
    rev = "f784257d0b9c316601440e4f02256bd6068e4f94";
    sha256 = "sha256-XYg0If1n6KKUtbJmdgakTdUzBxdMCMAK8XMBuX5DAfY=";
  };
  meta = {
    broken = false;
  };
})
