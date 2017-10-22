#!/bin/sh

for file in expected_images/*.png
do
    search=$(basename $file)
    cmp $file "test_images/$search"
done
