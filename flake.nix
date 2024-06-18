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
      in
      {
        packages = {
          guessing_game = ((import "${self}/guessing_game") { pkgs=nixpkgs.legacyPackages.${system}; });
        };

        devShells = {
          default = pkgs.mkShell {
            # Development tools
            packages = [
              pkgs.gcc14
              pkgs.clang
              pkgs.chez-racket
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
            '';

            # Tools from packages
            inputsFrom = [
              self.packages.${system}.guessing_game
            ];
          };
        };
      });
}
