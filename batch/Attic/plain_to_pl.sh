#!bin/bash

term_file=$2
a_file=$1

loaded_file="loaded.pl"
analyzed_file="analyzed.pl"

fixvalue() {
    if [ "$1" = "" ]; then
        echo "_"
    else
        echo $1
    fi
}

rm -f $term_file

mod_name=$(grep -F "Analyzing..." $a_file | awk -F'[' '{print $2}' | awk -F']' '{print $1}')

load_time=$(grep loaded $a_file | awk -v FS=" " '{print $3}')
load_time=$(fixvalue $load_time)

preprocess_time=$(grep preprocessed $a_file | awk -v FS=" " '{print $5}')
analysis_time=$(fixvalue $analysis_time)

analysis_time=$(grep analyzed $a_file | awk -v FS=" " '{print $5}')
analysis_time=$(fixvalue $analysis_time)

echo "t($mod_name, $load_time, $preprocess_time, $analysis_time, [err" >> $term_file
errors=$(grep ERROR $a_file)
if [ "$errors" != "" ]; then
    echo "l_error($a_file)" >> $loaded_file
    echo "a_error($a_file)" >> $analyzed_file
    
    grep ERROR $a_file | while read -r line ; do
        echo ", '$line'" >> $term_file 
    done
fi

echo "], [warn" >> $term_file

warns=$(grep WARNING $a_file)
if [ "$warns" != "" ]; then
    grep WARNING $a_file_error_analysis | while read -r line ; do
        echo ", '$line'" >> $term_file 
    done
fi

echo "])." >> $term_file

# arguments
#for i in "$@"
#do
#    echo "$i"
#done


