{
  description = "Category Theory for computing science notes";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
      in {
        defaultPackage = pkgs.cowsay;
        devShell = pkgs.mkShell {
          buildInputs = [ (pkgs.agda.withPackages (p: [ p.cubical ])) ];
          shellHook = ''
            export CUBICAL_AGDA_PATH=${pkgs.agdaPackages.cubical}
          '';
        };
      });
}
