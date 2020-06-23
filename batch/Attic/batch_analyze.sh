#!/usr/bin/env bash

# Physical directory where the script is located
_base=$(e=$0;while test -L "$e";do d=$(dirname "$e");e=$(readlink "$e");\
        cd "$d";done;cd "$(dirname "$e")";pwd -P)

datadir="$_base/../../data"

# ---------------------------------------------------------------------------

trap handle_int INT

function handle_int() {
    echo "Aborting analysis..."
    exit 1
}

# ---------------------------------------------------------------------------

function init_db() {
    mkdir -p "$datadir"
}

# TODO: move to bundle build rules instead
function ensure_ciaopp_batch_compiled() {
    # Compile ciaopp_batch
    echo "[commented compilation] (re)Compiling ciaopp_batch..."
    #ciaoc "$ciaopp_batch"
}

# ---------------------------------------------------------------------------

ciaopp_batch="$_base/ciaopp_batch"

msg_file="$datadir/analysis.txt"
server_file="$datadir/server_file.txt"
log_file="$datadir/analysis.log"

function do_analysis() { # [<paths>]
    ensure_ciaopp_batch_compiled

    echo "Start analysis..."
    init_db
    finished="false"
    while [ "$finished" != "true" ] ; do
        "$_base/control.sh" >> "$log_file" & #kills ciao if it takes more than 1 minute to analyze a module
        controlpid=$!
        "$ciaopp_batch" "$server_file" "$@" | tee "$msg_file"

        seenpid=$(ps -p $controlpid | grep control.sh | head -n 1 | awk '{print $1}')
        if [ x"$seenpid" == x"$controlpid" ]; then
            kill -TERM $controlpid
        fi

        finish_check=$(grep 'All modules analyzed' "$msg_file")

        if [ "$finish_check" != "" ] ; then
            finished="true"
        fi
    done

    rm -f "$msg_file"
#    echo $controlpid
    kill -TERM $controlpid &> /dev/null
    ciao clean-tree "$_base"
}

# ---------------------------------------------------------------------------

if [ $# == 0 ]; then
    cat <<EOF
Usage: batch_analyze.sh [<paths>]

where each path is a module or a directory containing modules to be
analyzed.

EOF
    exit 1
fi

do_analysis "$@"
