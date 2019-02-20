#!/usr/bin/env bash

set -x

printf 'travis_fold:start:main\\r'

./configure --hoqdir HoTT --coqbin coq/bin || exit 1
make -j 2

printf 'travis_fold:end:main\\r'
