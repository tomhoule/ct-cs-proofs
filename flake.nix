{
  description = "Category Theory for computing science notes";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
      in
      {
        defaultPackage = pkgs.cowsay;
        devShell = pkgs.mkShell {
          buildInputs = [ (pkgs.agda.withPackages (p: [ p.cubical ])) ];
          shellHook =
            let
              emacsPkg = pkgs.emacsWithPackages (p: [ p.agda2-mode ]);
            in
            ''
              alias emacs="${emacsPkg}/bin/emacs --no-init-file --load mini-init.el"
            '';
        };
      });
}


