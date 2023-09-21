<template>
	<template v-for="value, i of value">
		<template v-if=i>{{' '}}</template>
		<mysqlLeaf v-if=is_leaf(value) :name=`${name}[${i}]` :value=value :noSpace=true :option=fieldsOpted></mysqlLeaf>
		<mysqlExpr v-else :name=`${name}[${i}]` :value=value :noSpace=true></mysqlExpr>
	</template>
</template>

<script>
console.log('import mysqlArgs.vue');
import mysqlLeaf from "./mysqlLeaf.vue"

export default {
	components: {mysqlLeaf},//
	
	props : ['value', 'name', 'noSpace'],
	
	data(){
		return {};
	},

	created(){
		//var {value, name} = this;
		//console.log({value, name});
	},
	
	computed: {
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
		
		option() {
			return this.$parent.option;
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
		
		tables() {
			if (this.$data.tables)
				return this.$data.tables;
			return this.$parent.tables;	
		},
		
		databases() {
			return this.$parent.databases;	
		},
		
		numeric_operators() {
			return this.$parent.numeric_operators;
		},
		
		jsonobj_operators() {
			return this.$parent.jsonobj_operators;
		},
		
		numeric_relations() {
			return this.$parent.numeric_relations;
		},
		
		jsonobj_relations() {
			return this.$parent.jsonobj_relations;
		},

		textual_relations() {
			return this.$parent.textual_relations;
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
		
		numeric_function_regexp() {
			return this.$parent.numeric_function_regexp;
		},
		
		jsonobj_function_regexp() {
			return this.$parent.jsonobj_function_regexp;
		},

		textual_function_regexp() {
			return this.$parent.textual_function_regexp;
		},
		
		is_numeric_function() {
			return this.$parent.is_numeric_function;
		},
		
		is_jsonobj_function() {
			return this.$parent.is_jsonobj_function;
		},

		is_textual_function() {
			return this.$parent.is_textual_function;
		},
		 
		is_aggregate_function() {
			return this.$parent.is_aggregate_function;
		},

		is_numeric() {
			return this.function_is_numeric || this.is_numeric_operator || this.is_numeric_relation;
		},
		
		is_jsonobj() {
			return this.function_is_jsonobj || this.is_jsonobj_operator || this.is_jsonobj_relation;
		},

		fieldsOpted() {
			if (this.func == 'json_table')
				return '';

			return [...Object.keys(this.dtype), ...this.textual_functions];
		},
		
		operator() {
			return this.physic2logic(this.func);
		},
		
		is_numeric_relation(){
			var value = this.value[0];
			return value.gt || value.lt || value.ge || value.le; 
		},
		
		is_jsonobj_relation(){
			var value = this.value[0];
			return this.value.json_contains || this.value.json_contains_path; 
		},

		is_operator(){
			return this.is_numeric_operator || this.is_jsonobj_operator;
		},
		
		is_numeric_operator(){
			var value = this.value[0];
			return this.value.add || this.value.sub || this.value.mul || this.value.div || this.value.mod || this.value.AND || this.value.XOR || this.value.right_shift || this.value.left_shift;
		},
		
		is_jsonobj_operator(){
			var value = this.value[0];
			return this.value.json_extract || this.value.json_extract_unquote;
		},
		
		is_relation() {
			return this.is_numeric_relation || this.is_textual_relation || this.is_jsonobj_relation;
		},

		is_textual_relation(){
			var value = this.value[0];
			return value.regexp || value.like || value.regexp_binary || value.like_binary || value.not_regexp || value.not_like || value.not_regexp_binary || value.not_like_binary;
		},
		
		operatorsOpted() {
			return this.is_numeric_opeator ? this.numeric_operators: this.jsonobj_operators;
		},
		
		relationsOpted() {
			return this.is_numeric_relation ? this.numeric_relations: [...this.textual_relations, 'regexp_like', 'not regexp_like', ...this.jsonobj_relations];
		},
		
		functionsOpted() {
			var value = this.value[0];
			if (this.function_is_numeric)
				return this.numeric_functions;

			var option = [...this.textual_functions, ...this.jsonobj_functions];
			return option;
		},
		
		is_function() {
			return this.function_is_numeric || this.function_is_textual || this.function_is_jsonobj;
		},
		
		function_is_numeric() {
			return this.func.fullmatch(this.numeric_function_regexp);
		},
		
		function_is_jsonobj() {
			return this.func.fullmatch(this.jsonobj_function_regexp);
		},

		function_is_textual() {
			return this.func.fullmatch(this.textual_function_regexp);
		},
		
		is_logic(){
			var value = this.value[0];
			return value.and || value.or; 
		},
		
		func(){
			return this.$parent.func;
		},
		
		dtype() {
			return this.$parent.dtype;
		},
		
		desc() {
			return this.$parent.desc;
		},
		
		PRI() {
			return this.$parent.PRI;	
		},
		
		database() {
			return this.$parent.database;
		},
		
		change_input(){
			return this.$parent.change_input;
		},
		
		style_input(){
			return this.$parent.style_input;
		},
		
		input_kwargs(){
			return this.$parent.input_kwargs;
		},
		
		style_select() {
			return this.$parent.style_select;
		},
		
		component() {
			return this.$parent.component;
		},
	},
	
	methods: {
	},
};
</script>

<style>
</style>