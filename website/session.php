<?php
// foreach ($_POST as $key => $value){
//     echo "$key => $value<br>";
// }

require_once '../php/mysql.php';

$user = $_POST['login'];
$password = $_POST['password'];

$sql = "select * from login where user = '$user'";
foreach (mysql\select("select password from login where user = '$user'") as [$password_mysql]){
    if ($password == $password_mysql){
        break;
    }
    else{
        echo $sql."<br>";
        die("password incorrect, please try again!");
    }
}

?>
<script>
	var user = `<?php echo $user?>`;
	var href = location.href;
	href = href.match(/(.+)\/axiom\/website\/session\b/)[1]; 
	href = `${href}/${user}/index.php`;
	location.href = href;
</script>