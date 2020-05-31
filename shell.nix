let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};

  dhall = pkgs.stdenv.mkDerivation rec {
    name = "dhall-${version}";
    version = sources.dhall.version;
    src = sources.dhall;
    installPhase = ''
      mkdir -p $out/bin
      cp $src/* $out/bin/
    '';
  };
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    binutils cmake gcc gnumake openssl pkgconfig rustup
    niv dhall
  ];
}
