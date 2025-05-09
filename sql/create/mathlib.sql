CREATE TABLE `mathlib` (
  `name` varchar(256) NOT NULL PRIMARY KEY,
  `type` text,
  `instImplicit` text,
  `strictImplicit` text,
  `implicit` text,
  `given` json,
  `default` text,
  `imply` json NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY() PARTITIONS 8