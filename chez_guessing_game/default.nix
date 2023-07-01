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
    ${pkgs.chez-racket}/bin/scheme --script ../compile.scm $out/bin/${name}
  '';
  installPhase = ''
    chmod +x $out/bin/${name}
  '';
}
