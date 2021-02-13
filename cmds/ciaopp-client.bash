#!/bin/bash

# Client for ciaopp_daemon via HTTP
#
# Usage: ciaopp-client <ARGS>

# TODO:
#  - When ciaopp_daemon stops, /tmp/ciaopp_daemon.pid needs to be removed manually
#    
#  - Missing 100 Continue response, temporarily fixed with the "-H 'Expect:'" option
#    See https://stackoverflow.com/questions/30179476/where-is-a-delay-in-an-http-post-coming-from
#  - debug with '--trace - --trace-time' options in curl
#
#  - String escape args_to_json is not very robust

# Output input arguments as JSON string list 
function args_to_json() {
    if [ $# -eq 0 ]; then
        printf '[]'
        return
    else
        printf '["'
        esc_arg "$1"
        shift
        for i in "$@"; do
            printf '","'
            esc_arg "$i"
        done
        printf '"]'
    fi
}
function esc_arg {
    printf '%s' "${1//\"/\\\"}"
}

server=http://localhost:8000
daemon=ciaopp_daemon

# Encode arguments extended with '--cwd'
cwd=`realpath $(pwd)`
args=`args_to_json --cwd "$cwd" "$@"`
url=$server/$daemon

# Try 5 times before we have a good answer
for try in 1 2 3 4 5; do
    out=$(curl -s -H 'Expect:' -X POST \
               -F 'cmd='"$daemon"'.cmdrun' \
               -F 'data={"args":['"$args"']}' \
               "$url")
    if [ ${PIPESTATUS[0]} == 7 ]; then
        cat <<EOF 1>&2
ERROR: Could not connect to $daemon through the Ciao server

Please start it with \`ciao-serve' or \`M-x ciao-server-start' in emacs.
EOF
        exit 1
    fi
    case "$out" in
        '{"not_ready":"Connection refused"}'*) true ;;
        '{"not_ready":"No such file or directory"}'*) true ;;
        *) break ;;
    esac
    sleep 1
done

out=$(printf "%s" "$out" | sed \
    -e 's/^{"cont":.*"console","\(.*\)"]}}]}$/\1/' \
    -e 's/\\"/"/g' -e 's/\\n/\
/g') 
printf "%s\n" "$out"

