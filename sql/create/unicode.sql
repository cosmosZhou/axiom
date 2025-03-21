CREATE TABLE `unicode` (
  `unicode` varchar(12) NOT NULL COLLATE utf8mb4_bin PRIMARY KEY,
  `name` varchar(256),
  `latex` json
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY() PARTITIONS 8