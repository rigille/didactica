{ pkgs }:
pkgs.stdenv.mkDerivation rec {
  name = "guessing-game";
  src = ./.;
  propagatedBuildInputs = [
    pkgs.chez-racket
  ];
  buildPhase = ''
    mkdir -p $out/bin
    cd src
    ${chez-racket} --script ../compile.scm $out/bin/${name}
  '';
  installPhase = ''
  '';
}
