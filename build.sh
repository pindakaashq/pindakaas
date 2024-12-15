#!/usr/bin/env bash
set -e

root=$(pwd)
mkdir -p bin

scop="scop-for-xcsp23-230601-13h09m"
sr="savilerow-1.10.1-linux"

git submodule update --init --recursive

if [[ ! -d './bin/pindakaas/crates/pindakaas/res/ecm' ]]; then
  tar -xf bin/pindakaas/crates/pindakaas/res/ecm.tar.gz
  mv ecm ./bin/pindakaas/crates/pindakaas/res/
fi

if [[ ! -d './bin/fzn_picat/Picat' ]]; then
  cp -r bin/Picat bin/fzn_picat/
fi

if [[ ! -d "./bin/fun-scop" ]]; then
  cd bin
  wget https://tsoh.org/fun-scop/$scop.tar.gz
  tar -xf $scop.tar.gz
  rm $scop.tar.gz
  mv $scop fun-scop
  cd ..
fi

if [[ ! -d "./bin/savilerow" ]]; then
  cd bin
  wget "https://www-users.york.ac.uk/peter.nightingale/savilerow/$sr.tgz"
  tar -xf $sr.tgz
  rm $sr.tgz
  mv $sr savilerow
  cd ..
  cp ./savilerow ./bin/savilerow/savilerow
  ./bin/savilerow/savilerow -help
fi

cargo build --release
cargo t -r integration
