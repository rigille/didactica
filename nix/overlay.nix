final: prev: {
    coqPackages.VST = with prev; callPackage ./VST.nix {
          compcert = compcert.override {
            version = "3.13.1";
          };
          ITree = coqPackages.ITree.override {
            version = "4.0.0";
          };
          mkCoqDerivation = coqPackages.mkCoqDerivation;
       };
}
