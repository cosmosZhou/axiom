<?php
$company = $_POST['company'];
die(getenv("{$company}_API"));

/* 
for Linux:
```~/httpd/conf/httpd.conf
<VirtualHost *:8000>
    SetEnv MYSQL_USER "${MYSQL_USER}"
    SetEnv MYSQL_PROD "${MYSQL_PROD}"
    SetEnv DeepSeek_API "${DeepSeek_API}"
    SetEnv MyCompany_API "${MyCompany_API}"
</VirtualHost>
```
for Windows:
D:\wamp64\bin\apache\apache2.4.54.2\conf\extra\httpd-vhosts.conf

 */