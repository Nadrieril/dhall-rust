let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};

  # dhall = pkgs.stdenv.mkDerivation rec {
  #   name = "dhall-${version}";
  #   version = sources.dhall.version;
  #   src = sources.dhall;
  #   installPhase = ''
  #     mkdir -p $out
  #     cp -r $src/* $out/
  #   '';
  # };
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    binutils cmake gcc gnumake openssl zlib pkgconfig rustup
    niv
    # dhall
  ];
}
