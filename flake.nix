{
  description = "gitrees";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        coq = pkgs.coq_8_17;
        coqPkgs = pkgs.coqPackages_8_17;
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
              coqPkgs.equations
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
