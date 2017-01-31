#!/bin/sh
exec cabal install -j`nproc` regex-tdfa trifecta network
