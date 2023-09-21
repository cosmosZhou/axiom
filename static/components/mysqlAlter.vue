<template>
	<span class=alter>
		<select class=cmd v-model=$parent.cmd :style=style_select($parent.cmd)>
			<option v-for="value of cmds" :value=value>{{value}}</option>
		</select>
		<font color=blue> table </font>
		<mysqlDot v-focus :name="'alter[table]'" :value=value.alter.table></mysqlDot>
		<select class=operator v-model=operator :style="style_select(operator, 'red')">
			<option v-for="value of ['add', 'modify', 'drop']" :value=value>{{value}}</option>
		</select>&nbsp;
		<template v-for="operand, i of operand">
			<template v-if=i>,<br></template>
			<input v-model=operand[0] />&nbsp;
			<input v-model=operand[1] />&nbsp;
			comment<input v-model=operand[2] />&nbsp;
			after<input v-model=operand[3] />&nbsp;
		</template>
	</span>
</template>

<script>
console.log('import mysqlAlter.vue');
import {piece_together, is_number, is_enum, is_string, is_json} from "../js/mysql.js"
import mysqlExpr from "./mysqlExpr.vue"
import mysqlLeaf from "./mysqlLeaf.vue"
import mysqlDot from "./mysqlDot.vue"
import mysqlArgs from "./mysqlArgs.vue"

export default {
	components: {mysqlLeaf, mysqlExpr, mysqlDot, mysqlArgs},
	
	props : ['kwargs'],
	
	data(){
		var {$data} = this.$parent;
		return {
			...$data,
		};
	},

	created(){
		if (this.$parent.sql && !this.$parent.sql.match(/^alter /)) {
			var {data} = this.$parent.$parent;
			if (data && data.isArray)
				data.clear();

			setAttribute(this, 'sql', '');
		}
	},
	
	computed: {
		operand: {
			get() {
				return this.value[this.operator];	
			},
			
			set(operand) {
				this.value[this.operator] = operand;
			},
		},
		
		operator: {
			get() {
				for (var key in this.value) {
					if (key == 'alter')
						continue;
					return key;
				}
			},
			
			set(operator) {
				value = this.value.alter[this.operator];
				this.value.alter[operator] = value;
				delete this.value.alter[this.operator];
			}
		},
		
		size_input() {
			return Math.max(8, this.password.length, this.password_confirmed.length);
		},
		
		change_table(){
			return this.$parent.change_table;
		},
		
		change_database(){
			return this.$parent.change_database;
		},

		cmds() {
			return this.$parent.cmds;
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

		is_leaf() {
			return this.$parent.is_leaf;
		},		
		
		numericFields() {
			return this.$parent.numericFields;
		},
		
		textualFields() {
			return this.$parent.textualFields;
		},

		numeric_function_regexp() {
			return this.$parent.numeric_function_regexp;
		},
		
		jsonobj_function_regexp() {
			return this.$parent.jsonobj_function_regexp;
		},

		textual_function_regexp() {
			return this.$parent.textual_function_regexp;
		},

		is_aggregate_function() {
			return this.$parent.is_aggregate_function;
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
		
		where_dict() {
			return this.$parent.where_dict;
		},

		value() {
			return this.kwargs;
		},
		
		change_input(){
			return this.$parent.change_input;
		},
		
		style_select_table(){
			return this.$parent.style_select_table;
		},
		
		style_select(){
			return this.$parent.style_select;
		},
		
		style_input(){
			return this.$parent.style_input;
		},
		
		input_kwargs(){
			return this.$parent.input_kwargs;
		},
		
		PRI() {
			return this.$parent.PRI;
		},
		
		href_show() {
			var {host, user} = this;
			var url = [];
			url.push(`user=${user}`);
			if (host && host != 'localhost')
				url.push(`host=${host}`);			
			url.push(...piece_together(this.kwargs));
			return 'query.php?' + url.join('&');
		},		
	},
	
	methods: {
		keydown(event) {
			switch (event.key) {
			case 'Enter':
				this.error = this.password_confirmed != this.password;
				if (this.error) {
					this.password_confirmed = '';
					event.preventDefault();
				}
					
				break;
			}	
		},

		blur_input(event, print) {
			this.error = this.password_confirmed != this.password;
			if (this.error) {
				this.password_confirmed = '';
			}
		},
	},
	
	mounted(){
	},

	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	var element = el.querySelector('select[name]') || el.querySelector('input[name]');
		    	element.focus();
		    },
		},		
	},
}
</script>

<style>
select.password {
	color: blue;
}
</style>
