#!/bin/sh

cabalopts="--user -j`nproc` --ghc-options=-dynamic --lib"
set -ex
git submodule update --init
cabal install $cabalopts regex-posix trifecta network
cabal install $cabalopts ./hoopl
