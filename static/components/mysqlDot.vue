<template>
	<template v-if=database>
		<mysqlLeaf :value=database :option=databases :color="'navy'" :noSpace=true>
		</mysqlLeaf>.<mysqlLeaf :name=name_table :value=table :option=tables :color="'darkCyan'" :noSpace=noSpace>
		</mysqlLeaf>
	</template>	
	<mysqlLeaf v-else :name=name_table :value=table :option="tables.contains(table)? tables: null" :color="'darkCyan'" :noSpace=noSpace></mysqlLeaf>
</template>

<script>
console.log('import mysqlDot.vue');
import mysqlLeaf from "./mysqlLeaf.vue"
import {get_db_table, show_tables} from "../js/mysql.js"

export default {
	components: {mysqlLeaf},
	
	props : ['name', 'value', 'noSpace'],
	
	data(){
		return {
			_tables: null,
		};
	},

	created(){
		//var {databases, tables, database, table, name, value} = this;
		//console.log({databases, tables, database, table, name, value});
	},
	
	computed: {
		name_table() {
			var {database, name} = this;
			if (database)
				return `${name}[${database}]`;
			return name;
		},

		style_select() {
			return this.$parent.style_select;
		},
		
		is_textual_function() {
			return this.$parent.is_textual_function;
		},
		
		is_numeric_function() {
			return this.$parent.is_numeric_function;
		},
		
		is_jsonobj_function() {
			return this.$parent.is_jsonobj_function;
		},

		numeric_functions() {
			return this.$parent.numeric_functions;
		},
		
		jsonobj_functions() {
			return this.$parent.jsonobj_functions;
		},

		textual_functions() {
			return this.$parent.textual_functions;
		},
		
		input_kwargs() {
			return this.$parent.input_kwargs;
		},
		
		databases() {
			return this.$parent.databases;
		},

		tables: {
			get() {
				if (this._tables)
					return this._tables;
				return this.$parent.tables;
			},
			
			set(tables) {
				this._tables = tables;
			},
		},

		db_table() {
			return get_db_table(this.value);
		},
		
		database() {
			return this.db_table.database;
		},

		table() {
			return this.db_table.table;
		},
		
		host() {
			return this.$parent.host;
		},
		
		user() {
			return this.$parent.user;
		},
		
		token() {
			return this.$parent.token;
		},

		cmds() {
			return this.$parent.cmds;
		},
	},
	
	methods: {
		async input_select(event) {
			if (this.name.match(/(from|\[from\])$/)) {
				var {value} = event.target;
				if (value.fullmatch(new RegExp(this.databases.join('|')))) {
					if (this.$parent.$parent.change_database){
						this.$parent.$parent.change_database(event);
					}
					else {
						var database = value;
						this._tables = await show_tables(database, this.host, this.user, this.token);
					}
				}
				else {
					if (this.$parent.$parent.change_table){
						this.$parent.$parent.change_table(event);
					}
				}
			}
		},
	},
	
	mounted() {
	},
}
</script>