#!/usr/bin/env bash

# Physical directory where the script is located
_base=$(e=$0;while test -L "$e";do d=$(dirname "$e");e=$(readlink "$e");\
        cd "$d";done;cd "$(dirname "$e")";pwd -P)

datadir="$_base/../../data"

# ---------------------------------------------------------------------------

mkdir -p "$datadir"

server_file="$datadir/server_file.txt"
check_file="$datadir/last_analyzed_file.pl"
timeout=60

x=$(grep -F 'last_analyzed(' $check_file)
y=""
cont=0

while [ "$cont" != "$timeout" ] ; do
    if [ "$y" = "$x" ] ; then
        cont=$((cont + 1))
    else
        cont=0
        date
        echo $x
    fi
    y="$x"
    x=$(grep -F 'last_analyzed(' $check_file)
    sleep 1
done

function kill_ciaoengine_server() { # file
    local pid=`cat "$1"`
    local found=$(ps -p "$pid" | grep ciaoengine | head -n 1 | awk '{print $1}')
    if [ x"$found" == x"$pid" ]; then
        kill -TERM $pid
    fi
}

kill_ciaoengine_server "$server_file"

echo "Analysis timeout for: $x"

