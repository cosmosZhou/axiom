delete from mathlib;

load data local infile 'json/mathlib.tsv' into table mathlib character set utf8mb4;