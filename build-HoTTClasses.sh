#!/usr/bin/env bash

set -ex

printf 'travis_fold:start:main\\r'

./configure --hoqdir HoTT --coqbin coq/bin || exit 1
make -k -j "$NJOBS"

printf 'travis_fold:end:main\\r'
