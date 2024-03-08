{
  description = "Flake";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      lib = pkgs.lib;
      tex = pkgs.texlive.combine {
        inherit (pkgs.texlive) scheme-full
        biber
        biblatex
        cleveref
        dashbox
        environ
        gentium-tug
        ifmtarg
        iftex
        pbox
        scalerel
        totpages
        xifthen
        xstring;
      };
    in {
      packages = {        
        latex-artifact = pkgs.stdenvNoCC.mkDerivation rec {
          name = "latex-artifact";
          src = ./src;
          buildInputs = [ pkgs.coreutils tex ];
          phases = ["unpackPhase" "buildPhase" "installPhase"];
          buildPhase = ''
            export PATH="${lib.makeBinPath buildInputs}";
            mkdir -p .cache/texmf-var
            env TEXMFHOME=.cache TEXMFVAR=.cache/texmf-var \
              latexmk -interaction=nonstopmode -pdf -pdflatex \
              main.tex
          '';
          installPhase = ''
            mkdir -p $out
            cp main.pdf $out/
          '';
        };       
      };
      devShell = pkgs.mkShell {
        buildInputs = [
          tex
        ];
      };
    });
}
