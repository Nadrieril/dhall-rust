let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    binutils cmake gcc gnumake openssl pkgconfig rustup
    niv
  ];
}
