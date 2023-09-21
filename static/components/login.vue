<template>
	
	<form action="" method=post>
		<br>
		
		<div v-if=hidden_fields.length>
			<input v-for="[value, name] of hidden_fields" type=hidden :name=name :value=value />
			<p class=message>
				The action will be performed after successful login with the same credentials.
			</p>		
		</div>
		<table cellspacing=0 class=layout>
			<tr>
				<td colspan=2 class=center>
					Login Form
				</td>
			</tr>
		
			<tr>
				<th>Host</th>
				<td><input name=auth[host] v-model=host :title="`${host}:${port}`" placeholder=localhost autocapitalize=off /></td>
			</tr>
			<tr>
				<th>User</th>
				<td>
					<select v-focus name=auth[user] id=user v-model=user>
						<option v-for="value of ['user', 'test', 'prod', 'boss', 'root']">{{value}}</option>
					</select>
				</td>
			</tr>
			<tr>
				<th>Password</th>
				<td><input type=password name=auth[password] v-model=password autocomplete=current-password /></td>
			</tr>
			<tr>
				<th>Database</th>
				<td><input name=auth[db] v-model=db autocapitalize=off /></td>
			</tr>
			<tr>
				<th>Table</th>
				<td><input name=auth[table] v-model=table autocapitalize=off /></td>
			</tr>
			<p>
				<input type=submit value=Login />
				<label>
					permanently <input type=checkbox name=auth[permanent] v-model=permanent />
				</label>
			</p>
		</table>
		<h3>privileges allocated:</h3>
		<hr>
		<ul>
			<li>A user named <font color=blue>test</font> has <font color=red>select</font> privileges of dataset created by users of other users</li>
			<li>A user named <font color=blue>user</font> has <font color=red>select</font> privileges of dataset created by users of other users</li>
			<li>A user named <font color=blue>prod</font> has <font color=red>select/insert/delete/update</font> privileges of dataset created by users of other users</li>
			<li>A user named <font color=blue>boss</font> has <font color=red>select/insert/delete/update</font> privileges of dataset created by users of other users</li>
			<li>A user named <font color=blue>root</font> has <font color=red>select/insert/delete/update/create/alter/drop</font> privileges of dataset created by users of other users</li>
		</ul>		
	</form>
</template>

<script>
console.log('import login.vue');

export default {
	props: ['auth', 'hidden_fields'],

    components: {},
	
    data() {
        return {
        	mounted: {
        	},
        };
    },
    
    computed: {
    	port() {
    		return 3306;
    	},

    	host: {
    		get() {
    			return this.auth.host;
    		},

    		set(host) {
    			Object.assign(this.auth, {host});
    		},
    	},
    	
    	user: {
    		get() {
    			return this.auth.user;
    		},
    		set(user) {
    			Object.assign(this.auth, {user});
    		},
    	},
    	
    	password: {
    		get() {
    			return this.auth.password;
    		},
    		
    		set(password) {
    			Object.assign(this.auth, {password});
    		},
    	},
    	
    	db: {
    		get() {
    			return this.auth.db;
    		},
    		
    		set(db) {
    			Object.assign(this.auth, {db});
    		},
    	},
    	
    	table: {
    		get() {
    			return this.auth.table;
    		},
    		
    		set(table) {
    			Object.assign(this.auth, {table});
    		},
    	},

    	permanent: {
    		get() {
    			return this.auth.permanent;
    		},

    		set(permanent) {
    			Object.assign(this.auth, {permanent});
    		},
    	},    	
    },

    created() {
    	if (this.user == 'user' || this.user == 'prod') {
    		if (!this.password)
   				this.password = this.user;
    	}
    	
    	if (!this.table)
    		this.table = 'rlhf';
    },
    
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	el.focus();
		    },
		},		
	},		
    
}
</script>

<style>
body {
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;
	
	background-color: rgb(199, 237, 204);
	margin-left: 1.5em;
}

.message { color: green; background: #efe; }

.error, .message { padding: .5em .8em; margin: 1em 20px 0 0; }

form {
    margin-left: 4em;
}

table {
	margin-left: 8em;
    border-collapse: collapse;
    font-size: 120%;
    margin-bottom: 3em;
}

td.center {
    text-align: center;
    vertical-align: top;
    font-size: 1.5em;
    border-color: transparent transparent grey transparent;
    font-weight: bold;
    font-family: Times New Roman;
}

</style>
