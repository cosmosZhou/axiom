start_time=$(date +%s)
source ./sh/common.sh

__file__=$(realpath "$0")
user=$(dirname "$__file__")
user=$(basename "$user")
echo "user = $user"

> test.lean

declare -A imports_dict
function echo_import {
  file=$1
  lemma=${file%.lean}
  module=${lemma////.}
  echo "import $module" >> test.lean
  # extract import statements from the lean file
  module=${module#Axiom.}
  mapfile -t lines < <(grep -E '^import[[:space:]]+' $file | sed -E 's/^import[[:space:]]+//')
  if [ ${#lines[@]} -eq 0 ]; then
    imports_dict[$module]="[]"
  else
    imports_dict[$module]=$(printf '%s\n' "${lines[@]}" | jq -R . | jq -s .)
  fi
  # echo "imports_dict[$module] = " ${imports_dict[$module]}
}

while read -r file; do
  echo_import "$file"
done < <(find Axiom -type f -name "*.lean" -not -name "*.echo.lean" -not -name "Basic.lean") 

imports=$(cat test.lean)

touch test.log
lake setup-file test.lean Init $imports 2>&1 | \
  grep -v -E 'warning: .*\.lean:[0-9]+:[0-9]+: `[^`]+'\''` is missing a doc-string, please add one\.' | \
  grep -v "Declarations whose name ends with a \`'\` are expected to contain an explanation for the presence of a \`'\` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible." | \
  grep -v 'note: this linter can be disabled with `set_option linter.docPrime false`' | \
  tee test.log

sed -i -E "s/^import //" test.lean
imports=$(cat test.lean)
> test.lean

imports=($imports)
echo "modules:"
touch test.sql

echo "INSERT INTO lemma (user, module, imports, open, def, lemma, error, date) VALUES " > test.sql
for module in ${imports[*]}; do
  # echo "${module//.//}.lean"
  module=${module#Axiom.}
  if [ -z "${imports_dict[$module]}" ]; then
    echo "imports_dict[$module] = " ${imports_dict[$module]}
    continue
  fi
  echo "  ('$user', '$module', '${imports_dict[$module]}', '[]', '[]', '[]', '[]', '[]')," >> test.sql
done
sed -i '$ s/,$/\nON DUPLICATE KEY UPDATE imports = VALUES(imports), error = VALUES(error);/' test.sql

echo "plausible:"
sorryModules=($(grep -P "^warning: (\./)*[\w/]+\.lean:\d+:\d+: declaration uses 'sorry'" test.log | sed -E 's#^warning: ([.]/)*##' | sed -E "s/\.lean:[0-9]+:[0-9]+: declaration uses 'sorry'//" | sed 's#/#.#g'))
for module in ${sorryModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Axiom.}
  if [[ $module =~ ^sympy ]] || [[ $module =~ ^Basic ]]; then
    continue
  fi
  echo "UPDATE lemma set error = '[{\"code\": \"\", \"file\": \"\", \"info\": \"declaration uses ''sorry''\", \"line\": 0, \"type\": \"warning\"}]' where user = '$user' and module = '$module';" >> test.sql
done

echo "failed:"
failingModules=($(awk '/Some required builds logged failures:/{flag=1;next}/^[^-]/{flag=0}flag' test.log | sed 's/^- //'))
for module in ${failingModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Axiom.}
  if [[ $module =~ ^sympy ]] || [[ $module =~ ^Basic ]]; then
    continue
  fi
  echo "UPDATE lemma set error = '[{\"code\": \"\", \"file\": \"\", \"info\": \"\", \"line\": 0, \"type\": \"error\"}]' where user = '$user' and module = '$module';" >> test.sql
done

if [ -z "$MYSQL_USER" ]; then
  echo "MYSQL_USER is not set, acquiring it from ~/.bash_profile"
  source ~/.bash_profile
fi
if [ -z "$MYSQL_PORT" ]; then
  MYSQL_PORT="3306"
fi

mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -D axiom -e "update lemma set error = NULL" 2>&1 | tee test.log

grep -P "ERROR \d+ \(\d+\): Unknown database 'axiom'" test.log
if [ $? -eq 0 ]; then
  echo "CREATE DATABASE axiom;"
  mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -e "CREATE DATABASE axiom;"
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Database 'axiom' created successfully."
    bash $0 $*
    exit 0
  else
    echo "Failed to create database 'axiom'."
    exit 1
  fi
fi
mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -D axiom < test.sql 2>&1 | tee test.log
grep -P "ERROR \d+ \(\w+\) at line \d+: Table 'axiom.lemma' doesn't exist" test.log
if [ $? -eq 0 ]; then
  mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -D axiom < sql/create/lemma.sql
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Table 'lemma' created successfully."
    bash run.sh
    exit 0
  else
    echo "Failed to create table 'lemma'."
    exit 1
  fi
fi
mysql -u$MYSQL_USER -p$MYSQL_PASSWORD -P$MYSQL_PORT -D axiom -e "delete from lemma where error is NULL" 2>&1 | tee test.log
end_time=$(date +%s)
time_cost=$((end_time - start_time))

echo "seconds cost    = $time_cost"
echo "total theorems  = ${#imports[@]}"
echo "total plausible = ${#sorryModules[@]}"
echo "total failed    = ${#failingModules[@]}"

# post-processing

function remove_invalid_lake_file {
  module=${1#*/*/*/}
  module=${module%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    echo "rm $1, becase $module doesn't exist"
    rm $1
  fi
}

find .lake/build -type f -regex '.*\.\(trace\|olean\|ilean\|hash\|c\)$' | while read -r file; do
    remove_invalid_lake_file $file
done

function remove_invalid_echo_file {
  module=${1%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    echo "rm $1, becase $module doesn't exist"
    rm $1
  fi
}

find Axiom -type f -regex '.*\.echo\.lean$' | while read -r file; do
    remove_invalid_echo_file $file
done

find . -type d -empty -exec rmdir {} +
find .lake/build -type d -empty -exec rmdir {} +
