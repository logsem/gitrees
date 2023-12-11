{
  description = "gitrees";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.05;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        coq = pkgs.coq_8_17;
        coqPkgs = pkgs.coqPackages_8_17;
        ocamlPkgs = coq.ocamlPackages;
        stdpp-dev = coqPkgs.lib.overrideCoqDerivation
          {
            defaultVersion = "1.9.0";
            release."1.9.0".sha256 = "sha256-OXeB+XhdyzWMp5Karsz8obp0rTeMKrtG7fu/tmc9aeI=";
          } coqPkgs.stdpp;
        iris-dev = coqPkgs.mkCoqDerivation rec {
          pname = "iris";
          domain = "gitlab.mpi-sws.org";
          owner = "iris";
          defaultVersion = "4.1.0";
          release."4.1.0".sha256 = "sha256-nTZUeZOXiH7HsfGbMKDE7vGrNVCkbMaWxdMWUcTUNlo=";
          releaseRev = v: "iris-${v}";

          propagatedBuildInputs = [ stdpp-dev ];

          preBuild = ''
            if [[ -f coq-lint.sh ]]
            then patchShebangs coq-lint.sh
            fi
          '';
        };
      in {
        packages = {
          coq-artifact = coqPkgs.mkCoqDerivation {
            pname = "coq-artifact";
            version = "main";
            src = ./.;
            buildPhase = "make";
            propagatedBuildInputs = [
              stdpp-dev
              iris-dev
              coqPkgs.equations
            ];
          };
        };
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            coq
            stdpp-dev
            iris-dev
            coqPkgs.equations
          ];
        };
      });
}
