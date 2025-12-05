#!/bin/bash
usage() {
cat << EOF
Usage: 
  $0 problem part [-t test]
  Options:
    problem: The problem number, 1-25
    part: The problem part, 1 or 2
    test: optional 
EOF
}
re='^[0-9]+$'
if [ "$1" = "-h" ] || [ "$1" = "--help" ] || [ "$#" -lt 2 ] # Request help.
then
    usage
elif ! [[ $1 =~ $re ]] ; then
       echo "error: problem not a number"
       usage
       exit 2
elif ! [[ $2 =~ $re ]] ; then
       echo "error: part not a number"
       usage
       exit 2
elif ! [ -x "$(command -v dafny)" ]; then
    echo "error: Dafny not found in path"
else
    dafny run --no-verify --allow-warnings --unicode-char:true --target:cs "aoc-runner.dfy" --standard-libraries -- "$1" "$2" "$3"
fi
