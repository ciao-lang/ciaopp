#!bin/bash

check_file="last_analyzed_file.pl"

x=$(grep -F last_file $check_file)
y=""
cont=0

while [ "$cont" != "2" ] ; do
    if [ "$y" = "$x" ] ; then
        cont=$((cont + 1))
    else
        cont=0
    fi
    y="$x"
    x=$(grep -F last_file $check_file)
    sleep 1
done

pid=$(ps aux | grep 'sh control.sh' | head -n 1 | awk '{print $2}')

kill $pid

echo "[$pid] Analysis timeout for: $x"
