{ pkgs }:

{
  buildChezPackage = { package, name, src, buildInputs ? [], chez ? pkgs.chez, extraBuildInputs ? [] }:
    pkgs.stdenv.mkDerivation {
      inherit name src;
      
      buildInputs = [ chez ] ++ buildInputs ++ extraBuildInputs;
      
      buildPhase = ''
        export CHEZSCHEMELIBDIRS=$(find . -type d -printf '%p:' | sed 's/:$//')
        ${chez}/bin/scheme -q <<EOF
        (import (chezscheme))
        (optimize-level 2)
        (generate-wpo-files #t)
        (compile-imported-libraries #t)
        (compile-program "${package}/bin/${name}.scm")
        (compile-whole-program "${package}/bin/${name}.wpo" "${name}.so")
        (make-boot-file "${name}.boot" '("scheme" "petite") "${name}.so")
        (exit)
        EOF
      '';

      installPhase = ''
        mkdir -p $out/bin $out/lib
        cp ${name}.boot $out/lib
        echo '#!/bin/sh' > $out/bin/${name}
        echo '${chez}/bin/scheme --boot "'$out'/lib/${name}.boot" "$@"' >> $out/bin/${name}
        chmod +x $out/bin/${name}
      '';
    };
}
