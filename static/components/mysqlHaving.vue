<template>
	<font color=blue>having </font> 
	<template v-for="{aggregate, Field, operator, Type}, i of logics">
		<font v-if=i color=blue> and </font>
		<select :name="`having[aggregate][${Field}]`" :value=aggregate :style="style_select(aggregate, 'darkCyan')" @input=input_kwargs>
			<option v-for="value of ['count', 'sum', 'agv', 'min', 'max', 'group_concat', 'std', 'stddev_samp', 'variance', 'var_samp', 'var_pop', 'bit_and', 'bit_or', 'bit_xor', 'json_arrayagg', 'json_objectagg']" :value=value>{{value}}</option>
		</select>(<select :value=Field :style=style_select(Field) @input=input_select :index=i>
			<option value=''>{{underscore}}</option>
			<option v-for="value of desc.map(args => args.Field)" :value=value>{{value}}</option>
		</select>)
		<select :name="`having[operator][${Field}]`" :value=operator :style="style_select(operator, 'red')" @input=input_kwargs @change=change_select>
			<option v-for="op of operators(Type)" :value=op>{{op}}</option>
		</select>
		<input type=text :name="`having[${Field}]`" @change=change_input v-model=kwargs[Field] :style=style_input(Field) />
	</template>
</template>

<script>

console.log('import mysqlHaving.vue');
//import mysqlLookAround from "./mysqlLookAround.vue"
//https://dev.mysql.com/doc/refman/8.0/en/aggregate-functions.html
import {is_numeric, is_string, is_json} from "../js/mysql.js"

export default {
	components: {},
	
	props : [], 
	
	data(){
		return {
		};
	},

	created(){
		console.log(this.kwargs);
		console.log(this.logics);
	},
	
	computed: {
		host() {
			return this.$parent.host;
		},

		user() {
			return this.$parent.user;
		},
		
		style_select() {
			return this.$parent.style_select;
		},
		
		underscore() {
			var fields = this.desc.map(desc => desc.Field.length);
			if (fields.length)
				return '_'.repeat(max(fields));
			return '';
		},
		
		logics() {
			var logics = [];
			var {aggregate, operator} = this;
			for (var {Field} of this.desc) {
				if (this.kwargs[Field] != null) {
					logics.push({aggregate: aggregate[Field], Field, operator: operator[Field], Type: 'int'});
				}
			}
			
			if (!logics.length) {
				logics.push({aggregate: 'count', Field: '', operator: '=', Type: 'int'});
			}
			return logics;
		},
		
		PRI() {
			return this.$parent.PRI;
		},
		
		operator_value() {
			var operator_value = {};
			var {Field2Description} = this;
			for (var Field in Field2Description) {
				operator_value[Field] = this.get_operator_value(Field, Field2Description[Field].Type);
			}
			return operator_value;
		},
		
		Field2Description() {
			var Field2Description = {};
			for (var {Field, Type, Null, Key, Default, Extra} of this.desc) {
				Field2Description[Field] = {Type, Null, Key, Default, Extra};
			}
			return Field2Description;
		},
		
		look_behind() {
			var {look_behind} = this.kwargs;
			return look_behind? look_behind: {};
		},
		
		look_ahead() {
			var {look_ahead} = this.kwargs;
			return look_ahead? look_ahead: {};
		},
		
		style() {
			return this.$parent.style;
		},
		
		desc() {
			return this.$parent.desc;
		},
		
		json_extract() {
			return this.$parent.json_extract;
		},
		
		kwargs() {
			return this.$parent.kwargs.having;
		},
		
		dtype() {
			return this.$parent.dtype;
		},
		
		table() {
			return this.$parent.table;
		},
		
		limit: {
			get() {
				if (this.primary_key)
					return this.extra_kwargs.limit;
				return this.$parent.limit;
			},
			
			set(limit) {
				if (this.primary_key)
					this.extra_kwargs.limit = limit;
				else
					this.$root.limit = limit;
			}
		},
		
		offset: {
			get() {
				if (this.primary_key)
					return this.extra_kwargs.offset;
				return this.$parent.offset;
			},
			
			set(offset) {
				if (this.primary_key)
					this.extra_kwargs.offset = offset;
				else
					this.$root.offset = offset;
			},
		},
		
		change_table(){
			return this.$parent.change_table;
		},
		
		change_input(){
			return this.$parent.change_input;
		},
		
		style_select_table(){
			return this.$parent.style_select_table;
		},
		
		style_input(){
			return this.$parent.style_input;
		},
		
		input_kwargs(){
			return this.$parent.input_kwargs;
		},
		
		operator() {
			return this.kwargs.operator;
		},
		
		aggregate() {
			return this.kwargs.aggregate;
		},
	},
	
	methods: {
		input_select(event) {
			var {target} = event;
			var Field = target.value;
			var {kwargs} = this;
			if (this.kwargs[Field])
				return;
			
			var index = parseInt(target.getAttribute('index'));
			var {Field: oldField} = this.logics[index];
			
			var {aggregate, operator} = this;
			if (kwargs[oldField] == null) {
				kwargs[Field] = '';
				aggregate[Field] = 'count';
				operator[Field] = '=';
			}
			else {
				kwargs[Field] = kwargs[oldField];
				delete kwargs[oldField];
				
				aggregate[Field] = aggregate[oldField];
				delete aggregate[oldField];
				
				operator[Field] = operator[oldField];
				delete operator[oldField];
			}
		},

		change_select(event) {
			var {name, value} = event.target;
			name = name.split(/[\[\]]+/g).slice(1, -1);
			if (value.match(/regexp_like/)) {
				if (!this.operator.regexp_like)
					this.operator.regexp_like = {};

				if (!getitem(this.operator.regexp_like, ...name))
					setitem(this.operator.regexp_like, ...name,  'c');
			}
		},
		
		operator_name(Field) {
			if (this.primary_key)
				return `operator[${this.primary_key}][${this.value_name(Field)}]`;
			
			return `operator[${this.value_name(Field)}]`;
		},
		
		regexp_like_operator_name(Field) {
			if (this.primary_key)
				return `operator[regexp_like]${this.primary_key}[${Field}]`;
			return `operator[regexp_like][${Field}]`;
		},

		value_name(Field) {
			if (this.primary_key)
				return `${this.primary_key}[${Field}]`;

			return `${Field}${this.normalizeJsonExtract(this.json_extract[Field])}`;
		},
		
		operators(Type){
			if (is_numeric(Type))
				return ["=", "!=", ">", "<", ">=", "<="];
			
			var operators = [
				"regexp", "like", "regexp binary", "like binary", "=", "regexp_like", "find_in_set",
				"not regexp", "not like", "not regexp binary", "not like binary", "!=", "not regexp_like"
			];

			if (!is_json(Type))
				operators.push('in');
			
			return operators;
		},
		
		get_operator_value(Field, Type){
			if (this.operator){
				var value = this.operator[Field];
				if (value) {
					if (value.isString)
						return value;
					return "in";
				}
			}
			
			if (this.kwargs[Field] && !this.kwargs[Field].isString)
				return "in";
			
			if (is_string(Type))
				return 'regexp';

			if (is_json(Type)) {
				if (this.style[Field])
					return '=';
				return 'regexp';
			}

			return '=';
		},

		input_operator(event){
			var {name, value} = event.target;
			name = name.split(/[\[\]]+/);
			name = name.slice(1, -1);
			setitem(this.operator, ...name, value);
		},
		
		normalizeJsonExtract(s){
			if (s) {
				var digits = [];
				for (var m of s.matchAll(/\[\d+\]/g)) {
					digits.push(m[0]);
				}
				
				if (digits.length) {
					s = s.replace(/\[\d+\]/g, "%");
					return `->'$${s}'` + digits.join('');
				}
				
				return `->'$${s}'`;
			}
			else
				return '';
		},
		
		click(event){
			var Field = event.target.textContent;
			if (this.json_extract[Field]){
				delete this.json_extract[Field];
			}
			else{
				this.json_extract[Field] = ".";
			}
		},
	},
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	if (!location.hash) {
		    		var self = binding.instance;
		    		var mysql = self.$parent.$parent;
		    		if (mysql.focus != false)
		    			el.focus();
		    	}
		    },
		},
	},
}
</script>

<style>

button[type=button]{
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;
	background-color: inherit;
	-webkit-appearance: none;
	-moz-appearance: none;
	border-style: none;
	outline: none;
}

button[type=button]:hover{
	background-color: red;
}
</style>