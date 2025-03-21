SELECT 
  jt.latex
FROM 
  unicode 
CROSS JOIN JSON_TABLE(
  latex,
  '$[*]' COLUMNS (latex VARCHAR(255) COLLATE utf8mb4_0900_as_cs PATH '$')
) AS jt
WHERE 
  jt.latex IS NOT NULL
GROUP BY jt.latex
having 
  count(DISTINCT unicode) > 1
