{ pkgs ? (import <nixpkgs> {}).pkgs }:
with pkgs;
mkShell {
  buildInputs = [
    python3Packages.virtualenv # run virtualenv .
    python3Packages.matplotlib # avoid installing via pip
  ];
  shellHook = ''
    # fixes libstdc++ issues and libgl.so issues
    LD_LIBRARY_PATH=${stdenv.cc.cc.lib}/lib/
  '';
}

