{
  description = "Miscellaneous projects focused on good documentation and ease of understanding.";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      {
        packages = {
          guessing_game = ((import "${self}/guessing_game") { pkgs=nixpkgs.legacyPackages.${system}; });
        };

        devShells = {
          default = nixpkgs.mkShell {
            # Development tools
            packages = [
              nixpkgs.ocamlformat
              nixpkgs.ocamlPackages.odoc
              nixpkgs.ocamlPackages.ocaml-lsp
              nixpkgs.ocamlPackages.utop
            ];

            # Tools from packages
            inputsFrom = [
              self.packages.${system}.guessing_game
            ];
          };
        };
      });
}
