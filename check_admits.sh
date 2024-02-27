#! /bin/sh

grep -n -e 'admit' -e 'Admitted' $(find . -name '*.v' -type f)
