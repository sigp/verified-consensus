CREATE VIEW indirect_calls AS
WITH cte AS (
  SELECT c1.caller, c1.callee, 1 as lev
  FROM function_calls c1
  UNION ALL
  -- expand the graph out and increment the level, adding new edges that close the distance
  -- between two edges
  SELECT x.caller, c3.callee, lev + 1
  FROM cte x JOIN function_calls c3
  ON x.callee = c3.caller
)
SELECT *
FROM cte
ORDER BY cte.caller DESC;

CREATE VIEW indirect_reads AS
SELECT DISTINCT c.caller as function, r.field
FROM indirect_calls c JOIN direct_reads r
ON c.callee = r.function
UNION
SELECT f.name as function, r.field
FROM functions f JOIN direct_reads r
ON f.name = r.function
ORDER BY function DESC;

CREATE VIEW indirect_writes AS
SELECT DISTINCT c.caller as function, w.field
FROM indirect_calls c JOIN direct_writes w
ON c.callee = w.function
UNION
SELECT f.name as function, w.field
FROM functions f JOIN direct_writes w
ON f.name = w.function
ORDER BY function DESC;
