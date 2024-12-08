<template>
	<select value='group' @change=change_group style="color:blue">
		<option v-for="value of ['order', 'group']" :value=value>{{value}}</option>
	</select>
	<font color=blue> by </font>
	<mysqlLeaf v-if=dtype[group] :name="`${node_name('group')}`" :value=group :option=fieldsOpted></mysqlLeaf>
	<mysqlLeaf v-else-if=is_leaf(group) :name="`${node_name('group')}`" :value=group :noSpace=noSpace></mysqlLeaf>
	<mysqlExpr v-else :name="`${node_name('group')}`" :value=group :noSpace=noSpace></mysqlExpr>
	
	<template v-if=value.having>
		<font color=blue>having </font>
		<mysqlExpr :name="node_name('having')" :value=value.having></mysqlExpr>
	</template>
</template>

<script>
console.log('import mysqlGroup.vue');
import mysqlLeaf from "./mysqlLeaf.vue"

export default {
	components: {mysqlLeaf},
	props : [],
	
	data(){
		return {
		};
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
		
		group() {
			return this.value.group;
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

		is_aggregate_function() {
			return this.$parent.is_aggregate_function;
		},
		
		input_kwargs() {
			return this.$parent.input_kwargs;
		},

		style_select() {
			return this.$parent.style_select;
		},

		noSpace() {
			return this.$parent.noSpace;
		},
		
		fieldsOpted() {
			return Object.keys(this.dtype);
		},
		
		name() {
			return this.$parent.name;
		},
		
		value() {
			return this.$parent.value;
		},
		
		dtype() {
			return this.$parent.dtype;
		},
		
		PRI() {
			return this.$parent.PRI;
		},

		numericFields() {
			return this.$parent.numericFields;
		},
		
		textualFields() {
			return this.$parent.textualFields;
		},
		
		tables() {
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
		
		is_leaf() {
			return this.$parent.is_leaf;
		},
	},

	methods: {
		node_name(name, i) {
			if (this.name) {
				if (i == null)
					return `${this.name}[${name}]`;
				return `${this.name}[${name}][${i}]`;
			}

			if (i == null)
				return name;
			return `${name}[${i}]`;;
		},

		change_group(event) {
			delete this.value.group;
			delete this.value.having;
		},
	},
}
</script>