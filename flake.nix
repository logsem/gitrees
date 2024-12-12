{
  description = "gitrees";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-24.05;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        coq = pkgs.coq_8_19;
        coqPkgs = pkgs.coqPackages_8_19;
      in {
        packages = {
          coq-artifact = coqPkgs.mkCoqDerivation {
            pname = "coq-artifact";
            version = "main";
            src = ./.;
            buildPhase = "make";
            propagatedBuildInputs = [
              coqPkgs.stdpp
              coqPkgs.iris
            ];
          };
        };
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            coq
          ];
          inputsFrom = [ self.packages.${system}.coq-artifact ];
        };
      });
}
