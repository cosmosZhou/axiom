<template>
	<span class=show>
		<select class=cmd v-model=$parent.cmd :style=style_select($parent.cmd)>
			<option v-for="value of cmds" :value=value>{{value}}</option>
		</select>
		{{' '}}
		<mysqlExpr v-if=func v-focus :name="'show'" :value=value.show></mysqlExpr>
		<mysqlLeaf v-else v-focus :name="'show'" :value=value.show :option=aspects></mysqlLeaf>
	</span>
</template>

<script>
console.log('import mysqlShow.vue');
import {piece_together} from "../js/mysql.js"
import mysqlExpr from "./mysqlExpr.vue"
import mysqlLeaf from "./mysqlLeaf.vue"

/*
show databases;
show tables in corpus;
show create table corpus.markush;
show grants for test;
show global variables like '%regexp%';
show global status like '%schema%';
show variables like '%regexp%';
show status like '%schema%';
 */
 
export default {
	components: {mysqlLeaf, mysqlExpr},
	
	props : ['kwargs'],
	
	data(){
		var {$data} = this.$parent;
		return {
			...$data,
			aspects: ['tables', 'create', 'grants', 'status', 'variables', 'global', 'databases'],
		};
	},

	created(){
		if (this.$parent.sql && !this.$parent.sql.match(/^show /)) {
			var {data} = this.$parent.$parent;
			if (data && data.isArray)
				data.clear();

			setAttribute(this, 'sql', '');
		}
	},
	
	computed: {
		func() {
			var {show} = this.value;
			if (show.isString)
				return;
			return Object.keys(show)[0];
		},
		
		aspect: {
			get() {
				var {show} = this.value;
				if (show.isString)
					return show;
				
				if (show.in)
					return 'tables';
				
				if (show.for)
					return 'grants';
				
				if (show.like) {
					var [aspect] = show.like;
					if (aspect.isString)
						return aspect;
					return Object.keys(aspect)[0];
				}
					
				return Object.keys(show)[0];
			},
			
			set(aspect) {
				if (this.aspect == aspect)
					return;
				
				var {value} = this;
				switch (aspect) {
				case 'tables':
					delete value.show;
					value.show = {in: ['tables', 'corpus']};
					break;
					
				case 'create':
					delete value.show;
					value.show = {create: {table: {corpus: 'markush'}}};
					break;
					
				case 'grants':
					delete value.show;
					value.show = {for: [grants, 'root']};
					break;
					
				case 'status':
					delete value.show;
					value.show = {like: ['status', '%%']};
					break;
					
				case 'variables':
					delete value.show;
					value.show = {like: ['variables', '%%']};
					break;
					
				case 'global':
					delete value.show;
					value.show = {like: [{global: 'variables'}, '%%']};
					break;
					
				case 'databases':
					value.show = 'databases';
					break;
				}
			},
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
