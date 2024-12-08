start_time=$(date +%s)
source common.sh

__file__=$(realpath "$0")
user=$(dirname "$__file__")
user=$(basename "$user")
echo "user = $user"

> test.lean

function echo_import {
  theorem=${1%.lean}
  echo "import ${theorem////.}" >> test.lean
}

find Axiom -type f -name "*.lean" -print0 | while read -d $'\0' file; do
  echo_import "$file"
done

imports=$(cat test.lean)

touch test.log
lake setup-file test.lean Init $imports 2>&1 | tee test.log

sed -i -E "s/^import //" test.lean
imports=$(cat test.lean)
> test.lean

imports=($imports)
echo "modules:"
touch axiom.sql

echo "INSERT INTO axiom (user, axiom, state, lapse, latex) VALUES " > axiom.sql
for module in ${imports[*]}; do
  # echo "${module//.//}.lean"
  module=${module#Axiom.}
  if [[ $module =~ ^sympy ]] || [[ $module =~ ^Basic ]]; then
    continue
  fi
  echo "  ('$user', '$module', 'proved', '0', '')," >> axiom.sql
done
sed -i '$ s/,$/\nON DUPLICATE KEY UPDATE state = VALUES(state), lapse = VALUES(lapse), latex = VALUES(latex);/' axiom.sql


echo "plausible:"
sorryModules=($(grep -P "^warning: (\./)*[\w/]+\.lean:\d+:\d+: declaration uses 'sorry'" test.log | sed -E 's#^warning: ([.]/)*##' | sed -E "s/\.lean:[0-9]+:[0-9]+: declaration uses 'sorry'//" | sed 's#/#.#g'))
for module in ${sorryModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Axiom.}
  if [[ $module =~ ^sympy ]] || [[ $module =~ ^Basic ]]; then
    continue
  fi
  echo "UPDATE axiom set state = 'plausible' where user = '$user' and axiom = '$module';" >> axiom.sql
done

echo "failed:"
failingModules=($(awk '/Some required builds logged failures:/{flag=1;next}/^[^-]/{flag=0}flag' test.log | sed 's/^- //'))
for module in ${failingModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Axiom.}
  if [[ $module =~ ^sympy ]] || [[ $module =~ ^Basic ]]; then
    continue
  fi
  echo "UPDATE axiom set state = 'failed' where user = '$user' and axiom = '$module';" >> axiom.sql
done

if [ -z "$MYSQL_USER" ]; then
  echo "MYSQL_USER is not set, acquiring it from ~/.bash_profile"
  source ~/.bash_profile
fi
if [ -z "$MYSQL_PORT" ]; then
  MYSQL_PORT=""
else
  MYSQL_PORT="-P$MYSQL_PORT"
fi

mysql -u$MYSQL_USER -p$MYSQL_PASSWORD $MYSQL_PORT -D axiom < axiom.sql 2>&1 | tee test.log

grep -P "ERROR \d+ \(\d+\): Unknown database 'axiom'" test.log
if [ $? -eq 0 ]; then
  echo "CREATE DATABASE axiom;"
  mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -e "CREATE DATABASE axiom;"
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Database 'axiom' created successfully."
    bash run.sh
    exit 0  
  else
    echo "Failed to create database 'axiom'."
    exit 1
  fi
fi

grep -P "ERROR \d+ \(\w+\) at line \d+: Table 'axiom.axiom' doesn't exist" test.log
if [ $? -eq 0 ]; then
  sql="CREATE TABLE axiom (
  user varchar(32) NOT NULL,
  axiom varchar(256) NOT NULL,
  state enum('proved', 'failed', 'plausible', 'unproved', 'unprovable', 'slow') NOT NULL,
  lapse double default NULL,
  latex mediumblob NOT NULL,
  PRIMARY KEY (user, axiom)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY() PARTITIONS 8"
  echo $sql
  mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -D axiom -e "$sql;"
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Table 'axiom' created successfully."
    bash run.sh
    exit 0
  else
    echo "Failed to create table 'axiom'."
    exit 1
  fi
fi
end_time=$(date +%s)
time_cost=$((end_time - start_time))

echo "seconds cost    = $time_cost"
echo "total theorems  = ${#imports[@]}"
echo "total plausible = ${#sorryModules[@]}"
echo "total failed    = ${#failingModules[@]}"

# post-processing

function remove_invalid {
  module=${1#*/*/*/}
  module=${module%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    echo "rm $1, becase $module doesn't exist"
    rm $1
  fi
}

find .lake/build -type f -regex '.*\.\(trace\|olean\|ilean\|hash\|c\)$' | while read -r file; do
    remove_invalid $file
done

find . -type d -empty -exec rmdir {} +
find .lake/build -type d -empty -exec rmdir {} +
