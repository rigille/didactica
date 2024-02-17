{
  description = "Miscellaneous projects focused on good documentation and ease of understanding.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?rev=b4fd387395d0124d936cfcde67ad08206b229b91";
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
              pkgs.chez-racket
              pkgs.coq_8_16
              pkgs.coqPackages_8_16.VST
              #pkgs.coqPackages.topology
            ];

            # Tools from packages
            inputsFrom = [
              self.packages.${system}.guessing_game
            ];
          };
        };
      });
}
