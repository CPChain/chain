#!/bin/sh

set -e

if [ ! -f "build/env.sh" ]; then
    echo "$0 must be run from the root of the repository."
    exit 2
fi

# Create fake Go workspace if it doesn't exist yet.
workspace="$PWD/build/_workspace"
root="$PWD"
cpchaindir="$workspace/src/bitbucket.org/cpchain"
if [ ! -L "$cpchaindir/chain" ]; then
    mkdir -p "$cpchaindir"
    cd "$cpchaindir"
    ln -s ../../../../../. chain
    cd "$root"
fi

# Set up the environment to use the workspace.
GOPATH="$workspace"
export GOPATH

# Run the command inside the workspace.
cd "$cpchaindir/chain"
PWD="$cpchaindir/chain"

# Launch the arguments with the configured environment.
exec "$@"
