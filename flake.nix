{
  description = "Iris tutorial development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in
    {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          # OPAM tool and build dependencies
          opam
          gmp
          pkg-config
          rsync
          unzip
          patch

          # Rocq & language server (Commented out because installed via opam)
          # rocq-core
          # rocqPackages.stdlib
          # rocqPackages.stdpp
          # rocqPackages.iris
          # rocqPackages.vsrocq-language-server

          gawk
          git
        ];

        shellHook = ''
          # Automatically load opam environment variables if an opam switch exists
          eval $(opam env 2>/dev/null)
        '';
      };

      checks.${system}.default = pkgs.stdenv.mkDerivation {
        name = "iris-tutorial-check";
        src = ./.;
        nativeBuildInputs = with pkgs; [
          rocq-core
          rocqPackages.stdlib
          rocqPackages.stdpp
          rocqPackages.iris
          gawk
          git
        ];
        buildPhase = ''
          make -j$NIX_BUILD_CORES all
          make exercises
          make html
        '';
        installPhase = ''
          mkdir -p $out/share/doc
          cp -r html $out/share/doc/html
          touch $out/done
        '';
      };
    };
}
