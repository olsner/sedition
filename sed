#!/bin/sh

exec cabal run sedition:exe:sedition -v0 -- "$@"
