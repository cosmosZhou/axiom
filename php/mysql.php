<?php
// use the following regex to remove error_log prints:
// ^ *error_log
namespace mysql;

include_once 'std.php';
use mysqli, Exception, std;
use std\Text, std\Set, std\Queue, std\Graph;

function desc_table($table)
{
    return get_rows("desc $table");
}

function sift_data($table, &$data)
{
    //error_log('$table = '.$table);
    $desc = desc_table($table);
    //error_log('$desc = '.std\encode($desc));
    $key2id = [];
    $id2key = [];
    foreach (std\range(0, count($desc)) as $i) {
        $Field = $desc[$i]['Field'];
        $Key = $desc[$i]['Key'];
        if ($Key == 'PRI')
            $PRI = $Field;
        
        $key2id[$Field] = $i;
        $id2key[$i] = $Field;
    }
    
    //error_log('$PRI = '.$PRI);
    //error_log('$key2id = '.std\encode($key2id));
    
    $primary_keys = [];
    $PRI2obj = [];
    foreach ($data as &$obj) {
        $dict = [];
        foreach (std\enumerate($obj) as [$i, $arg]) {
            $dict[$id2key[$i]] = $arg;
        }
        $primary_key = $obj[$key2id[$PRI]];
        $primary_keys[] = $primary_key;
        //error_log('$dict = '.std\encode($dict));
        $PRI2obj[$primary_key] = $dict;
    }
    
    //error_log('$PRI2obj = '.std\encode($PRI2obj));
    $primary_keys_str = implode(",", array_map(fn($primary_key) => "'$primary_key'", $primary_keys));
    //error_log('$primary_keys_str = '.$primary_keys_str);
    if (count($primary_keys) == 1) {
        $sql = "select * from $table where $PRI = $primary_keys_str";
    }
    else {
        $sql = "select * from $table where $PRI in ($primary_keys_str)";
    }
    
    //error_log("sql: $sql");
    $difference = [];
    foreach (get_rows($sql) as &$that_obj) {
        $primary_key = $that_obj[$PRI];
        //error_log('$primary_key = '.$primary_key);
        
        $this_obj = &$PRI2obj[$that_obj[$PRI]];
        //error_log('$this_obj = '.std\encode($this_obj));
        
        if (empty(array_diff($this_obj, $that_obj)) && empty(array_diff($that_obj, $this_obj)))
            continue;
        
        error_log('difference detected:');
        error_log('$this_obj = '.std\encode($this_obj));
        error_log('$that_obj = '.std\encode($that_obj));
        $difference[] = &$that_obj;
    }
    //error_log('$difference: '.std\encode($difference));
    return $difference;
}

function load_data($table, &$data, $replace = false, $ignore=true, $step = 1000)
{
    if (is_array($data)) {
        return load_data_from_list($table, $data, $replace, $ignore, $step);
    } else if ($data){
        return load_data_from_csv($table, $data, $replace, $ignore);
    }
}

function load_data_from_list($table, &$array, $replace = true, $ignore = false, $step = 1000, $truncate = false)
{
    $desc = desc_table($table);

    $has_training_field = False;

    $char_length = array_fill(0, count($desc), 256);
    $dtype = array_fill(0, count($desc), null);
    foreach (std\range(0, count($desc)) as $i) {        
        $Field = $desc[$i]['Field'];
        $Type = $desc[$i]['Type'];
        $dtype[$i] = $Type;

        if ($Field == 'training') {
            $has_training_field = True;
        }

        if ($Type == 'text' || $Type == 'json') {
            $char_length[$i] = 65535;
        }

        elseif ($Type == 'mediumblob') {
            $char_length[$i] = 16 * 1024 * 1024 - 1;
        }
        
        elseif (preg_match("/varchar\((\d+)\)/", $Type, $m)) {
            $char_length[$i] = (int) $m[1];
        }
    }

    $folder = sys_get_temp_dir();
    $rowcount = 0;
    foreach (std\range(0, count($array), $step) as $i) {
        $csv = $folder . "/$table-$i.csv";

        $file = new Text($csv);
        foreach (array_slice($array, $i, $step) as $args) {
            if (!std\is_list($args))
                $args = array_map(fn(&$desc) => std\get($args, $desc['Field'], ''), $desc);

            foreach (std\range(count($args)) as $i) {
                $arg = $args[$i];
                if (is_array($arg)) {
                    $bytes = std\substring(std\encode(std\encode($arg)), 1, -1);
                }
                elseif (is_string($arg)) {
                    $bytes = std\substring(std\encode($arg), 1, -1);
                }
                elseif ($arg === null) {
                    $bytes = "null";
                } else {
                    $bytes = "$arg";
                }

                if (! $ignore) {
                    if (is_varchar($dtype[$i])) {
                        if (std\len($arg) > $char_length[$i]) {
                            if ($truncate) {
                                error_log('truncating the data to maximum length: '.$char_length[$i].", since its length is ".std\len($arg));
                                $arg = substr($arg, 0, $char_length[$i]);
                                $bytes = std\substring(std\encode($arg), 1, -1);
                            } else {
                                error_log(std\encode($args));
                                error_log("args[$i] exceeds the allowable length: " . $char_length[$i].", since its length is ".std\len($arg));
                                $args = null;
                                break;
                            }
                        }
                    }
                    else {
                        if (strlen($bytes) > $char_length[$i]) {
                            if ($truncate) {
                                error_log('truncating the data to maximum length: '.char_length[$i].", since its length is ".strlen($arg));
                                $bytes = substr($bytes, 0, $char_length[$i]);
                            } else {
                                error_log(std\encode($args));
                                error_log("args[$i] exceeds the allowable length " . $char_length[$i]);
                                $args = null;
                                break;
                            }
                        }
                    }
                }

                $args[$i] = $bytes;
            }

            if ($args != null) {
                if ($has_training_field && count($args) < count($desc)) {
                    $args[] = "" . rand(0, 1);
                }

                $line = join("\t", $args);
                $file->append($line);
            }
        }
        $file->flush();

        $rowcount += load_data_from_csv($table, $csv, $replace, $ignore);
    }

    error_log('$rowcount = '.$rowcount);
    return $rowcount;
}

function load_data_from_csv($table, $csv, $replace = false, $ignore = true, $delete = True)
{
    $start = time();
    $csv = str_replace('\\', '/', $csv);

    if ($replace)
        $sql = "load data local infile '$csv' replace into table $table character set utf8mb4";
    else if ($ignore)
        $sql = "load data local infile '$csv' ignore into table $table character set utf8mb4";
    else
        $sql = "load data local infile '$csv' into table $table character set utf8mb4";
// add the following line into ~/php/etc/php.ini  / D:\wamp64\bin\apache\apache2.4.39\bin\php.ini (Windows Version);
// mysqli.allow_local_infile = On

// add the following line into my.ini;
// [mysql]
// local-infile=1
// [mysqld]
// local-infile=1

    $local_infile = True;
    foreach (get_rows("show global variables like 'local_infile'") as $obj) {
        $Variable_name = $obj['Variable_name'];
        $Value = $obj['Value'];
        assert($Variable_name == 'local_infile', "Variable_name == 'local_infile'");
        if ($Value == 'OFF')
            $local_infile = False;
    }
    
    if (!$local_infile)
        execute('set global local_infile = 1');

    try {
        error_log("executing ".$sql);
        $rowcount = execute($sql);
    } catch (Exception $e) {
        error_log($e->getMessage());
        $rowcount = 0;
    }

//     if (!$rowcount && $connection['error'] == 'Malformed packet') {
//         $password = get_password();
//         $user = $_GET['user'];
//         $host = HOST;
//         [$host, $port] = explode(":", $host, 2);
        
//         $result_file = $csv.'.txt';
//         $cmd = "mysql --local_infile=1 -h$host --port=$port -u$user -p$password -e\"$sql; select row_count();\" > $result_file";
//         //error_log('$cmd = '.$cmd);
//         $ret = shell_exec($cmd);        
//         $content = file_get_contents($result_file);
//         //error_log('sql $content = '.$content);
//         [$title, $rowcount] = explode("\n", $content);
//         $rowcount = (int)$rowcount;
//         try {
//             unlink($result_file);
//         } catch (Exception $e) {
//             // error_log($e->getMessage());
//         }
//     }

    error_log('time cost = '.(time() - $start));
    if ($delete) {
        error_log("os.remove(csv) ".$csv);
        try {
            unlink($csv);
        } catch (Exception $e) {
            // error_log($e->getMessage());
            return;
        }
    }

    return $rowcount;
}

function multi_query($sql, $batch = true)
{
    //error_log("sql = " . implode(";", $sql));
    global $connection;

    if ($batch) {
        if (is_array($sql))
            $sql = implode(';', $sql);

        if (! $sql)
            return 0;

        $result = $connection->multi_query($sql);
        if ($result === false) {
            error_log("error occurred in");
            error_log("sql = " . $sql);
            error_log($connection->error);
            return 0;
            // throw new Exception($connection->error);
        }

        $array = [];
        do {
            $result = $connection->store_result();
            if ($result instanceof mysqli_result) {

                $rows = [];
                while ($row = $result->fetch_assoc()) {
                    // while ($row = $result->fetch_row()){}
                    $rows[] = $row;
                }
                $array[] = $rows;

                error_log(std\encode($rows));
            } else {
                $array[] = $connection->affected_rows;
            }
        } while ($connection->more_results() && $connection->next_result());

        return array_sum($array);
    } else {
        if (is_string($sql))
            $sql = explode(';', $sql);

        if (! $sql)
            return 0;

        $rowcount = 0;
        foreach ($sql as $line) {
            execute($line);
            $rowcount += $connection->affected_rows;
        }
        
        return $rowcount;
    }
}

function execute($sql, &$resulttype = MYSQLI_NUM)
{
    global $connection;
    try {
        $array = $connection->query($sql);
    }
    catch (Exception $e) {
        error_log($e->getMessage());
        return 0;
    }
    
    if ($array === true) {
        return $connection->affected_rows;
    }

    if ($array === false) {
        error_log("error occurred in executing:");
        error_log($sql);
        error_log($connection->error);
        if (is_array($resulttype)) {
            $resulttype['error'] = $connection->error;
        }
        return 0;
    }
    
    $result = [];
    while ($row = $array->fetch_array($resulttype)) {
        $result[] = $row;
    }

    return $result;
}

function insertmany($table, $matrix, $replace = true)
{
    $insert = $replace ? 'replace' : 'insert';

    $sql = "$insert into $table values" . implode(",", array_map(fn ($vector) => "(" . substr(std\encode($vector), 1, - 1) . ")", $matrix));
    // error_log("sql = $sql");
    return execute($sql);
}

function scan_data($sql, $resulttype, $fn, $limit, &$offset) // the other choice is MYSQLI_ASSOC
{
    $result = [];
    $count = 0;

    if ($resulttype === true) {
        $resulttype = MYSQLI_ASSOC;
    }

    $result_mode = MYSQLI_USE_RESULT;
    global $connection;

    // error_log("sql = $sql");
    $array = $connection->query($sql, $result_mode);

    while ($row = $array->fetch_array($resulttype)) {
        ++ $offset;
        // error_log("\$offset = ".$offset);
        if ($fn($row)) {
            $result[] = $row;

            if (++ $count >= $limit) {
                $connection->__destruct();
                return $result;
            }
        }
    }

    return $result;
}

class ConnectMysqli
{

    public static $instance = null;

    private $link;

    private function __construct()
    {
        $config = parse_ini_file(dirname(__file__) . "/config.ini", true)['client'];
        // error_log(std\encode($config));

        $this->link = new mysqli($config['host'], $config['user'], $config['password'], $config['database']);
        if (! $this->link) {
            die('Could not connect: this->link is null');
        }
        if ($this->link->connect_error)
            die('Could not connect: ' . $this->link->connect_error);

        $this->link->query("set names utf8");
    }

    public function commit()
    {
        $this->link->commit();
    }

    public function __destruct()
    {
        // echo 'closing mysql!<br>';
        if ($this->link) {
            $this->link->close();
            $this->link = null;
        }
    }

    private function __clone()
    {
        die('clone is not allowed');
    }

    public static function getInstance()
    {
        if (self::$instance == null) {
            self::$instance = new self();
        }
        return self::$instance;
    }

    public function query($sql, $result_mode = MYSQLI_STORE_RESULT)
    {
        $array = $this->link->query($sql, $result_mode);
        if ($array === false) {
            error_log("erroneous sql = " . $sql);
            throw new Exception($this->link->error);
        }
        return $array;
    }

    public function multi_query($sql)
    {
        if (is_array($sql))
            $sql = implode(';', $sql);

        if (! $sql)
            return [0];

        $link = $this->link;
        $result = $link->multi_query($sql);
        if ($result === false) {
            error_log("sql = " . $sql);
            return [0];
            // throw new Exception($link->error);
        }

        $array = [];
        do {
            $result = $link->store_result();
            if ($result instanceof mysqli_result) {

                $rows = [];
                while ($row = $result->fetch_row()) {
                    // while ($row = $result->fetch_assoc()){}
                    $rows[] = $row;
                }
                $array[] = $rows;

                error_log(std\encode($rows));
            } else {
                $array[] = $link->affected_rows;
            }
        } while ($link->more_results() && $link->next_result());

        return $array;
    }

    public function getInsertid()
    {
        return $this->link->insert_id;
    }

    /**
     *
     * @param
     * @return string or int
     */
    public function getOne($sql)
    {
        $query = $this->query($sql);
        return mysqli_free_result($query);
    }

    public function getRow($sql, $type = "assoc")
    {
        $query = $this->query($sql);
        if (! in_array($type, ["assoc", 'array', "row"])) {
            die("mysqli_query error");
        }
        $funcname = "mysqli_fetch_" . $type;
        return $funcname($query);
    }

    public function getFormSource($query, $type = "assoc")
    {
        if (! in_array($type, ["assoc", "array", "row"])) {
            die("mysqli_query error");
        }
        $funcname = "mysqli_fetch_" . $type;
        return $funcname($query);
    }

    public function getAll($sql)
    {
        $query = $this->query($sql);
        $list = [];
        while ($r = $this->getFormSource($query)) {
            $list[] = $r;
        }
        return $list;
    }

    /**
     *
     * @param string $table
     * @param
     */
    public function insert($table, $data)
    {
        $key_str = '';
        $v_str = '';
        foreach ($data as $key => $v) {
            if (empty($v)) {
                die("error");
            }
            $key_str .= $key . ',';
            $v_str .= "'$v',";
        }
        $key_str = trim($key_str, ',');
        $v_str = trim($v_str, ',');
        $sql = "insert into $table ($key_str) values ($v_str)";
        $this->query($sql);
        return $this->getInsertid();
    }

    /*
     */
    public function deleteOne($table, $where)
    {
        if (is_array($where)) {
            foreach ($where as $key => $val) {
                $condition = $key . '=' . $val;
            }
        } else {
            $condition = $where;
        }
        $sql = "delete from $table where $condition";
        $this->query($sql);
        return mysqli_affected_rows($this->link);
    }

    /*
     */
    public function deleteAll($table, $where)
    {
        if (is_array($where)) {
            foreach ($where as $key => $val) {
                if (is_array($val)) {
                    $condition = $key . ' in (' . implode(',', $val) . ')';
                } else {
                    $condition = $key . '=' . $val;
                }
            }
        } else {
            $condition = $where;
        }
        $sql = "delete from $table where $condition";
        $this->query($sql);
        return mysqli_affected_rows($this->link);
    }

    /**
     *
     * @return [type]
     */
    public function update($table, $data, $where)
    {
        $str = '';
        foreach ($data as $key => $v) {
            $str .= "$key='$v',";
        }
        $str = rtrim($str, ',');
        $sql = "update $table set $str where $where";
        $this->query($sql);
        return mysqli_affected_rows($this->link);
    }
}

function is_int($Type)
{
    return preg_match('/int\(\d+\)/', $Type);
}

function is_float($Type)
{
    return preg_match('/double/', $Type);
}

function is_number($Type)
{
    return preg_match('/int|double/', $Type);
}

function is_varchar($Type)
{
    if (preg_match('/varchar\((\d+)\)/', $Type, $m))
        return (int)$m[1];
}

function is_json($Type)
{
    return preg_match('/json/', $Type);
}

function is_enum($Type)
{
    return preg_match('/enum\((\S+)\)/', $Type);
}

function mysqlStr($value, $Type = '', $quote=true)
{
    if (! is_number($Type)) {
        $value = str_replace("'", "''", $value);
        if ($Type != 'regexp') {
            $value = preg_replace("/((?<![\\\\])[\\\\](?![ntvr\"\\\\])|[\\\\]{2,})/", '$1$1', $value);
            if ($Type == 'json')
                $value = preg_replace('/[\\\\]([n"])/', '\\\\\\\\$1', $value);
        }
        else {
            $value = preg_replace("/((?<![\\\\])[\\\\](?![ntv\"\\\\]))/", '$1$1', $value);
        }

        if ($quote)
            $value = "'$value'";
    }

    return $value;
}

function is_admin()
{
    $remote_addr = $_SERVER['REMOTE_ADDR'];
    if (in_array($remote_addr, ['::1', '127.0.0.1', '192.168.5.21']))
        return true;

    error_log("$remote_addr is not among the hosts allowable");
    return false;
}

function get_primary_key($table)
{
    foreach (select("desc ${table}", true) as $desc) {
        $key = $desc['Field'];
        if ($desc['Key'] == 'PRI')
            return $key;
    }
}

function show_create_table($database, $table)
{
    if ($database) {
        $table = "$database.$table";
    }

    [[$table_name, $createTableSQL]] = get_rows("show create table ${table}");
    return [$table_name, $createTableSQL];
}

function show_collation($database, $table)
{
    [$table_name, $createTableSQL] = show_create_table($database, $table);

    preg_match("/COLLATE=(\w+)/", $createTableSQL, $m);
    return $m[1];
}

function is_collation_case_sensitive($table)
{
    return preg_match("/_cs$/", show_collation($table), $m);
}

function is_collation_case_insensitive($database, $table)
{
    return preg_match("/_ci$/", show_collation($database, $table), $m);
}

function field_to_type($database, $table)
{
    $Field2Type = [];
    if ($database) {
        $table = "${database}.${table}";
    }

    $indexKey = [];
    $transform = [];
    foreach (get_rows("show full columns from $table", true) as $desc) {
        $Field = $desc['Field'];
        $Key = $desc['Key'];
        if ($Key) {
            $indexKey[$Field] = true;

            if ($Key == 'PRI')
                $primary_key = $Field;
        }

        $Field2Type[$Field] = $desc['Type'];

        $Comment = $desc['Comment'];
        if ($Comment) {
            $Comment = json_decode($Comment, true);
            if ($fn = $Comment['transform']) {
                $transform[$Field] = $fn;
            } else {
                $transform[$Field] = 'entity';
            }
        }
    }

    return [$Field2Type, $primary_key, $indexKey, $transform];
}

function json_decode_by_field_to_type($Field2Type, &$data)
{
    foreach ($Field2Type as $Field => $Type) {
        if ($Type == 'json') {
            foreach ($data as &$dict) {
                $value = &$dict[$Field];
                if (! is_array($value)) {
                    $value = std\decode($value);
                }
            }
        }
    }
}

function aggregate_type($type)
{
    switch ($value) {
    case "count":
    case 'bit_and':
    case 'bit_or':
    case 'bit_xor':
        return 'int';

    case 'sum':
    case 'agv':
    case 'min':
    case 'max':
    case 'std':
    case 'stddev_samp':
    case 'variance':
    case 'var_samp':
    case 'var_pop':
        return 'float';

    case 'group_concat':
        return 'text';

    case 'json_arrayagg':
    case 'json_objectagg':
    case 'json_remove':
        return 'json';

    default:
        break;
    }
}
?>