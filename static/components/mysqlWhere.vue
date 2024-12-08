<template>
	{{' '}}<font color=blue>where</font> 
	<template v-for="{Field, Type, Null, Key, Default, Extra}, i of desc">
		<font v-if=i color=blue>and</font>
		<template v-if="Array.isArray(dtype[Field])">
			<template v-if="dtype[Field] == 'json'">
				<button type=button @click=click :title="json_extract[Field]? 'click to collapse fields' : 'click to extract json fields'">{{Field}}</button>
				<template v-if=json_extract[Field]>->'$<input v-model=json_extract[Field] :size="Math.max(json_extract[Field].length, 5)" />'</template>
			</template>
			<template v-else>{{' ' + Field + ' '}}</template>
		
			<select :name="`operator[${Field}]`" :value=operator_value[Field] :style=style_select_operator(Field) @input=input_operator>
				<option v-for="value of ['=', '!=']" :value=value>{{value}}</option>
			</select>
			<select :name=Field v-model=kwargs[Field] @input=input_kwargs :style=style_select(Field)>
				<option value=''>{{'_'.repeat(Math.max(...dtype[Field].map(el => el.length)))}}</option>
				<option v-for="value of dtype[Field]" :value=value>{{value}}</option>
			</select>
		</template>
		<template v-else-if=style[Field]>
			<template v-if="dtype[Field] == 'json'">
				<button type=button @click=click :title="json_extract[Field]? 'click to collapse fields' : 'click to extract json fields'">{{Field}}</button>
				<template v-if=json_extract[Field]>->'$<input v-model=json_extract[Field] :size="Math.max(json_extract[Field].length, 5)" />'</template>
			</template>
			<template v-else>{{' ' + Field + ' '}}</template>
			
			<select :name="`operator[${Field}]`" :value=operator_value[Field] :style=style_select_operator(Field) @input=input_operator>
				<option v-for="value of ['=', '!=']" :value=value>{{value}}</option>
			</select>
			<select :name=Field :value="kwargs[Field] == null? '': kwargs[Field]" @input=input_kwargs :style="`${style_select(Field)}; ${style[Field][kwargs[Field]]}`">
				<option value=''>{{'_'.repeat(Math.max(...Object.keys(style[Field]).map(el => el.length)))}}</option>
				<option v-for="(style, value) in style[Field]" :value=value :style=style>{{value}}</option>
			</select>
		</template>
		<template v-else>
			<template v-if="operator_value[Field] == 'regexp_like'">&nbsp;<select :name=operator_name(Field) :value=operator_value[Field] :style=style_select_operator(Field) @input=input_operator>
					<option v-for="op of operators(Type)" :value=op>{{op}}</option>
				</select>(<template v-if="dtype[Field] == 'json'">
					<button type=button @click=click :title="json_extract[Field]? 'click to collapse fields' : 'click to extract json fields'">{{Field}}</button>
					<template v-if=json_extract[Field]>->'$<input v-model=json_extract[Field] :size="Math.max(json_extract[Field].length, 5)" />'</template>
				</template><template v-else>{{Field}}</template>,
				<mysqlLookAround :Field=Field></mysqlLookAround>
				<template v-if="operator.regexp_like && operator.regexp_like[Field]">, 
					<select :name=regexp_like_operator_name(Field) :value=operator.regexp_like[Field] @input=input_operator>
						<option v-for="op of ['i', 'c', 'n', 'm', 'x']" :value=op>{{op}}</option>
					</select>
				</template>)
			</template>
			<template v-else>
				<template v-if="dtype[Field] == 'json'">
					<button type=button @click=click :title="json_extract[Field]? 'click to collapse fields' : 'click to extract json fields'">{{Field}}</button>
					<template v-if=json_extract[Field]>->'$<input v-model=json_extract[Field] :size="Math.max(json_extract[Field].length, 5)" />'</template>
				</template>
				<template v-else>{{' ' + Field + ' '}}</template>
			
				<select :name=operator_name(Field) :value=operator_value[Field] :style=style_select_operator(Field) @input=input_operator @change=change_select>
					<option v-for="op of operators(Type)" :value=op>{{op}}</option>
				</select>
				<template v-if="operator_value[Field] == 'in'">(select {{Field}} from {{table}}
					<mysqlWhere :extra_kwargs="kwargs[Field]? kwargs[Field]: {}" :primary_key=Field></mysqlWhere>)
				</template>
				<mysqlLookAround v-else-if=operator_value[Field].match(/regexp/) :Field=Field></mysqlLookAround>
				<input v-else v-focus type=text :name=value_name(Field) @change=change_input v-model=kwargs[Field] :style=style_input(Field) />
			</template>
		</template>
	</template> 
	<mysqlGroup v-if=group :group=group :Field=Field></mysqlGroup>
	<mysqlOrder v-else :order=order :desc=desc :Field=Field></mysqlOrder>
</template>

<script>

console.log('import mysqlWhere.vue');
import mysqlOrder from "./mysqlOrder.vue"
import mysqlGroup from "./mysqlGroup.vue"
import mysqlLookAround from "./mysqlLookAround.vue"

import {is_numeric, is_string, is_json} from "../js/mysql.js"

export default {
	components: {mysqlOrder, mysqlLookAround, mysqlGroup},
	
	props : ['extra_kwargs', 'primary_key'], //used in primary_key search
	
	data(){
		return {
		};
	},

	created(){
	},
	
	computed: {
		style_limit(){
			var length = this.limit? this.limit.toString().length / 2 + 0.5: 1;
			length = Math.max(2, length);
			return `width: ${length}em`;
		},

		style_offset(){
			var length = this.offset ? this.offset.toString().length / 2 + 0.5 : 2;
			length = Math.max(2, length);
			return `width: ${length}em`;
		},
		
		PRI() {
			return this.$parent.PRI;
		},
		
		operator_value() {
			var operator_value = {};
			var {Field2Description} = this;
			for (var Field in Field2Description) {
				operator_value[Field] = this.get_operator_value(Field, Field2Description[Field].Type, Field2Description[Field].Key);
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
			if (this.extra_kwargs)
				return this.extra_kwargs;
			return this.$parent.kwargs;
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
		
		order: {
			get() {
				if (this.primary_key)
					return this.extra_kwargs.order;
				return this.$parent.order;
			},
			
			set(order) {
				if (this.primary_key)
					this.extra_kwargs.order = order;
				else
					this.$parent.order = order;
			},
		},
		
		group: {
			get() {
				if (this.primary_key)
					return this.extra_kwargs.group;
				return this.$parent.group;
			},
			
			set(group) {
				if (this.primary_key)
					this.extra_kwargs.group = group;
				else
					this.$parent.group = group;
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
		
		style_select() {
			return this.$parent.style_select;
		},
	},
	
	methods: {
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
		
		get_operator_value(Field, Type, Key){
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
			
			if (is_json(Type)) {
				if (this.style[Field])
					return '=';
				return 'regexp';
			}

			if (Key)
				return '=';
			
			if (is_string(Type))
				return 'regexp';

			return '=';
		},

		style_select_operator(Field){
			return this.style_select(this.operator_value[Field], 'red');
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