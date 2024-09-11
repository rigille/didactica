{ pkgs }:

{
  buildChezPackage = { package, name, src, optimize-level ? 2, buildInputs ? [], chez ? pkgs.chez, extraBuildInputs ? [] }:
    pkgs.stdenv.mkDerivation {
      inherit name src;
      
      buildInputs = [ chez ] ++ buildInputs ++ extraBuildInputs;
      
      buildPhase = ''
        export CHEZSCHEMELIBDIRS=$(find . -type d -printf '%p:' | sed 's/:$//')
        ${chez}/bin/scheme -q <<EOF
        (import (chezscheme))
        (optimize-level ${toString optimize-level})
        (generate-wpo-files #t)
        (compile-imported-libraries #t)
        (compile-program "${package}/bin/${name}.ss")
        (compile-whole-program "${package}/bin/${name}.wpo" "${name}.so")
        (make-boot-file "${name}.boot" '("scheme" "petite") "${name}.so")
        (exit)
        EOF
      '';

      installPhase = ''
        mkdir -p $out/bin $out/lib
        cp ${name}.boot $out/lib
        find . -type f -name "*.so" -print0 | xargs -0 -I {} cp {} $out/lib
        echo '#!/bin/sh' > $out/bin/${name}
        echo '${chez}/bin/scheme --boot "'$out'/lib/${name}.boot" --libdirs "'$out'/lib" "$@"' >> $out/bin/${name}
        chmod +x $out/bin/${name}
      '';
    };
}
