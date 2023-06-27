{
  description = "Nix setup for verification using HOL4, and compilation using CakeML";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    holsrc = {
      url = "github:HOL-Theorem-Prover/HOL?rev=56875629a42860effd84a80abd66e63a4c7a4961";
      flake = false;
    };
    cakemlsrc = {
      url = "github:cakeml/cakeml?rev=a500b998760b855e6d32428c2e39ce0f69a89131";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, holsrc, cakemlsrc }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; overlays = [
        (final: prev: {
          polyml = prev.polyml.overrideAttrs (attrs: {
            configureFlags = [ "--enable-shared" ];
          });})
      ];};

  in {
    packages.${system} = rec {
      hol4 = pkgs.stdenv.mkDerivation {
        name = "hol4";
        src =  holsrc;
        buildInputs = (with pkgs; [ polyml graphviz fontconfig ]);
        installPhase = ''
          chmod --recursive a-w "$out" || true
        '';
        buildPhase = ''
          mkdir -p "$out"
          cp --recursive $src/* "$out/"
          chmod --recursive +w "$out"
          cd $out

          export HOLDIR="$(pwd)"

          # necessary until including kananaskis-14
          substituteInPlace tools/Holmake/Holmake_types.sml \
            --replace '"/bin/' '"'

          poly < tools/smart-configure.sml
          ./bin/build --fullbuild

          {
          cat <<EOF
          examples/algorithms
          examples/algorithms/unification/triangular/first-order
          examples/balanced_bst
          examples/bootstrap
          examples/Crypto/AES
          examples/Crypto/RC6
          examples/Crypto/TEA
          examples/formal-languages/regular
          examples/formal-languages/context-free
          examples/formal-languages
          examples/fun-op-sem/lprefix_lub
          examples/l3-machine-code/common
          examples/machine-code/decompiler
          examples/machine-code/hoare-triple
          examples/machine-code/multiword
          examples/miller/miller
          EOF
          } | while read -r dir; do
            echo ":: building HOLDIR/$dir"
            cd "$HOLDIR/$dir" && $HOLDIR/bin/Holmake
          done

          {
          cat <<EOF
          examples/algorithms
          examples/algorithms/unification/triangular/first-order
          examples/balanced_bst
          examples/bootstrap
          examples/Crypto/AES
          examples/Crypto/RC6
          examples/Crypto/TEA
          examples/formal-languages/regular
          examples/formal-languages/context-free
          examples/formal-languages
          examples/fun-op-sem/lprefix_lub
          examples/l3-machine-code/common
          examples/machine-code/decompiler
          examples/machine-code/hoare-triple
          examples/machine-code/multiword
          examples/miller/miller
          EOF
          } | while read -r dir; do
            echo ":: building HOLDIR/$dir"
            cd "$HOLDIR/$dir" && $HOLDIR/bin/Holmake
          done

        '';
      };

      cakeml = pkgs.stdenv.mkDerivation {
        name = "CakeML";
        src =  cakemlsrc;
        # dependencies gcc, gnumake and glibc are loaded by default
        buildInputs = [ hol4 ] ++ (with pkgs; [ gcc gnumake glibc ]);
        # glibc with _FORTIFY_SOURCE>0 causes build of basis_ffi.c to fail
        hardeningDisable = [ "fortify" ];
        buildPhase = ''
          mkdir --parents "$out"
          cp --recursive $src/* "$out/"
          chmod --recursive +w "$out"
          cd $out

          export HOLDIR="${hol4}"
          export CAKEMLDIR="$(pwd)"

          {
          cat <<EOF
          developers
          misc
          semantics
          basis/pure
          characteristic
          translator
          translator/monadic
          compiler/parsing
          basis
          unverified/sexpr-bootstrap
          EOF
          } | while read -r dir; do
            echo ":: building CAKEMLDIR/$dir"
            cd "$CAKEMLDIR/$dir" && "$HOLDIR/bin/Holmake" -k
          done

          {
          cat <<EOF
          developers
          misc
          semantics
          basis/pure
          characteristic
          translator
          translator/monadic
          compiler/parsing
          basis
          unverified/sexpr-bootstrap
          EOF
          } | while read -r dir; do
            echo ":: building CAKEMLDIR/$dir"
            cd "$CAKEMLDIR/$dir" && "$HOLDIR/bin/Holmake" -k
          done

        '';
        installPhase = ''
          true
        '';
      };

      cakemlbin = pkgs.stdenv.mkDerivation rec {
        name = "cakeml-bin-${version}";
        version = "2157";

        # https://nixos.wiki/wiki/Packaging/Binaries
        src = pkgs.fetchurl {
          url = "https://github.com/CakeML/cakeml/releases/download/v${version}/cake-x64-64.tar.gz";
          sha256 = "sha256-km5LetIytSVFftWlO0kMEubnVv0jozvWJHz6r30lPLI=";
        };
        buildInputs = with pkgs; [ gcc gnumake glibc ];

        # glibc with _FORTIFY_SOURCE>0 causes build of basis_ffi.c to fail
        hardeningDisable = [ "fortify" ];

        installPhase = ''
          install -m755 -D -t $out cake
          install -m555 -D -t $out \
            basis_ffi.c Makefile cake-sexpr-32 cake-sexpr-64
        '';

        meta = with pkgs.lib; {
          homepage = "https://cakeml.org";
          description = "A verified implementation of ML";
          platforms = platforms.linux;
        };
      };

      default = pkgs.stdenv.mkDerivation {
        pname = "test nix ci";
        version = "1.2.3";
        src = self;
        buildInputs = [ hol4 cakeml cakemlbin ];
        # glibc with _FORTIFY_SOURCE>0 causes build of basis_ffi.c to fail
        hardeningDisable = [ "fortify" ];
        buildPhase = ''
          mkdir --parents "$out"
          cp --recursive "$src"/* "$out/"
          chmod --recursive +w "$out"
          cd $out

          export HOLDIR="${hol4}"
          export CAKEMLDIR="${cakeml}"
          export CAKEDIR="${cakemlbin}"
          make
        '';
        installPhase = ''
          true
        '';
      };
    };
  };
}

