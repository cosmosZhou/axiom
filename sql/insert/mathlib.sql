-- Create a temporary table with the same schema as the original (minus partitioning)
CREATE TEMPORARY TABLE temp_mathlib (PRIMARY KEY (`name`)) 
AS SELECT * FROM mathlib LIMIT 0;  -- Inherits columns and data types (no indexes/partitions)

-- Load the data into the temporary table
load data local infile 'json/mathlib.tsv' into table temp_mathlib 
character set utf8mb4 
FIELDS TERMINATED BY '\t' 
LINES TERMINATED BY '\n';

-- Update existing rows where `type` has changed
update
  mathlib
  join temp_mathlib using (`name`)
set 
  mathlib.`type` = temp_mathlib.`type`,
  mathlib.`instImplicit` = temp_mathlib.`instImplicit`,
  mathlib.`strictImplicit` = temp_mathlib.`strictImplicit`,
  mathlib.`implicit` = temp_mathlib.`implicit`,
  mathlib.`given` = temp_mathlib.`given`,
  mathlib.`default` = temp_mathlib.`default`,
  mathlib.`imply` = temp_mathlib.`imply`
where
  mathlib.`type` != temp_mathlib.`type`;

-- Insert new rows that don't exist in the original table
INSERT INTO mathlib
SELECT temp_mathlib.*
FROM 
  temp_mathlib
  LEFT JOIN mathlib using (`name`)
WHERE mathlib.name is null;

-- Update the `imply` column to ensure it is not null
update
  mathlib
set 
  imply = '{}'
where 
  imply is null or imply like 'null';

-- Delete rows in mathlib that are not present in the temporary table
DELETE m 
FROM mathlib as m
LEFT JOIN temp_mathlib as _t using (name)
WHERE _t.name is null;

-- Cleanup
DROP TEMPORARY TABLE IF EXISTS temp_mathlib;
