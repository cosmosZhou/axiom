<template>
	<select value='order' @change=change_order style="color:blue">
		<option v-for="value of ['order', 'group']">{{value}}</option>
	</select>
	<font color=blue> by </font>
	
	<mysqlLeaf v-if=dtype[order] :name=name_order :value=order :option=fieldsOpted :noSpace=noSpace></mysqlLeaf>
	<mysqlLeaf v-else-if=is_leaf(order) :name=name_order :value=order :noSpace=noSpace :option=fieldsOpted></mysqlLeaf>
	<mysqlExpr v-else :name=name_order :value=order :noSpace=noSpace></mysqlExpr><template v-if=sort>
		<font> </font>
		<mysqlLeaf :name=name_sort :value=sort :option="['asc', 'desc']" :noSpace=true></mysqlLeaf>
	</template>
</template>

<script>
console.log('import mysqlOrder.vue');
import mysqlLeaf from "./mysqlLeaf.vue"

export default {
	components: {mysqlLeaf},
	
	props : ['noSpace'],
	
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
			return [...Object.keys(this.dtype), {function: ['rand', 'length', 'char_length']}];
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
		
		PRI() {
			return this.$parent.PRI;	
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
		
		order(){
			var {order} = this.value;
			if (order) {
				if (order.isString)
					return order;
				
				if (order.isArray)
					return order[0];

				return order;
			}
		},
		
		sort(){
			var {order} = this.value;
			if (order) {
				if (order.isString)
					return '';
				
				if (order.isArray)
					return order[1];
			}
		},
		
		name_order(){
			var {order} = this.value;
			if (order) {
				if (order.isString)
					return this.node_name('order');
			}
			
			return this.node_name('order', 0);
		},
		
		name_sort(){
			return this.node_name('order', 1);
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
		
		change_order(event) {
			delete this.value.order;
			delete this.value.having;
			this.value.group = this.PRI;
		},
	},
}
</script>

<style scoped>
</style>