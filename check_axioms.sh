#! /bin/sh
grep -n -e 'Axiom' $(find . -name '*.v' -type f)
