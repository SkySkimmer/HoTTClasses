#!/usr/bin/env bash

############ Caching #############
# Storing cache is handled by travis
# We need to invalidate the cache ourselves

# git ls-remote gets us the desired commit hash

# git rev-parse HEAD gets us the cached one if it exists

# If we need to rebuild we just rm -rf the directory, that way we
# don't deal with historical artefacts

function get_latest {
    git ls-remote --exit-code "$1" "refs/heads/$2" | awk '{print $1}';
}

set -xe

printf 'travis_fold:start:cache.check\\r'

#NB: always use SkySkimmer/HoTT because I can have PRs not yet merged
#in HoTT/HoTT and ejgallego/HoTT
COQ_URL="https://github.com/mattam82/coq.git"
COQ_BRANCH="IR"
HOTT_URL="https://github.com/SkySkimmer/HoTT.git"
HOTT_BRANCH="mz-8.7"

if [ -d coq ];
then
    pushd coq
    LATEST_COQ=$(get_latest "$COQ_URL" "$COQ_BRANCH")
    CURRENT_COQ=$(git rev-parse HEAD)
    popd
    if [ "$LATEST_COQ" != "$CURRENT_COQ" ];
    then
        # we need to rebuild HoTT if Coq is changed
        rm -rf coq HoTT
    fi
fi

if [ -d HoTT ];
then
    pushd HoTT
    LATEST_HOTT=$(get_latest "$HOTT_URL" "$HOTT_BRANCH")
    CURRENT_HOTT=$(git rev-parse HEAD)
    popd
    if [ "$LATEST_HOTT" != "$CURRENT_HOTT" ];
    then rm -rf HoTT
    fi
fi

printf 'travis_fold:end:cache.check\\r'

if ! [ -d coq ]
then
    echo 'Building Coq...'
    printf 'travis_fold:start:coq.build\\r'

    git clone --depth 1 -b "$COQ_BRANCH" -- "$COQ_URL" coq
    pushd coq
    ./configure -local || exit 1
    make -j "$NJOBS" tools coqbinaries pluginsopt states || exit 1
    popd

    printf 'travis_fold:end:coq.build\\r'
else
    echo "Using cached Coq."
fi

if [ ! "(" -d HoTT ")" ];
then
    echo 'Building HoTT...'
    printf 'travis_fold:start:HoTT.build\\r'

    git clone --depth 1 -b "$HOTT_BRANCH" -- "$HOTT_URL" HoTT
    pushd HoTT

    # don't let autogen clone some other Coq
    mv .git .git-backup
    ./autogen.sh
    mv .git-backup .git

    ./configure COQBIN="$(pwd)/../coq/bin/" || exit 1
    make -j "$NJOBS" || exit 1
    popd

    printf 'travis_fold:end:HoTT.build\\r'
else
    echo "Using cached HoTT."
fi
