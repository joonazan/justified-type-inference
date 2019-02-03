{ pkgs ? import <nixpkgs> {} }:

with pkgs;

stdenv.mkDerivation {
  name = "idris-env";

  buildInputs = [
    (idrisPackages.with-packages (with idrisPackages; [ contrib pruviloj ]))
    gmp
  ];
}
