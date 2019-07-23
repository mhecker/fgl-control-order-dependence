#!/bin/bash

cat $1 | sed -e 's/\\172/¬/g' | sed -e 's/\\8804/≤/g' | sed -e 's/\\\"\([^\"]\)\\\"/\1/g'  > $1.utf8 ; xdot $1.utf8

