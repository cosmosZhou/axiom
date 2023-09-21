<template>
	<span v-if=value.from>
		<template v-if=value.with>
			<span v-html=indent_with></span><font color=blue>with </font>
			<mysqlExpr v-if=value.with.isArray v-for="value, i of value.with" :name="node_name('with', i)" :value=value></mysqlExpr>
			<mysqlExpr :name="node_name('with')" :value=value.with></mysqlExpr><br>
		</template>

		<span v-html=indent_select></span>
		<select class=cmd v-model=cmd @keydown=keydown_cmd>
			<option v-for="value of cmds" :value=value>{{value}}</option>
		</select>{{' '}}

		<template v-if=!value.select></template>
		<template v-else-if=value.select.isArray v-for="value, i of value.select">
			<template v-if=i>, </template>
			<mysqlLeaf v-if=value.isString :name="`${node_name('select', i)}`" :value=value :option=option :noSpace=true></mysqlLeaf>
			<mysqlExpr v-else :name="`${node_name('select', i)}`" :value=value :noSpace=true></mysqlExpr>
		</template>
		<mysqlLeaf v-else-if=value.select.isString :name="node_name('select')" :value=value.select :option=option :noSpace=true></mysqlLeaf>
		<mysqlExpr v-else :name="node_name('select')" :value=value.select :noSpace=true></mysqlExpr>		

		<font color=blue> from </font>
		<template v-if=join_type>
			<mysqlDot :name="node_name('from')" :value=join_table[0]></mysqlDot>
		
			<select class=join_type v-model=join_type>
				<option v-for="value of ['inner', 'cross', 'left', 'right', 'full']" :value=value>{{value}}</option>
			</select><font color=blue> join </font>
			<mysqlLeaf v-if="is_leaf(join_table[1])" :name=join_name :value=join_table[1] :option=option_join></mysqlLeaf>
			<mysqlExpr v-else :name=join_name :value=join_table[1]></mysqlExpr>
		</template>
		<template v-else>
			<template v-if=value.from.from>
				(<mysqlExpr :name="node_name('from')" :value=value.from :noSpace=true></mysqlExpr>)
			</template>
			<mysqlDot v-else :name="node_name('from')" :value=value.from></mysqlDot>
		</template>
		
		<template v-if=value.where>
			<font color=blue>where </font>
			<mysqlExpr :name="node_name('where')" :value=value.where :noSpace=true></mysqlExpr>
		</template>
		
		<template v-if="'group' in value">
			{{' '}}
			<mysqlGroup :noSpace=true></mysqlGroup>
		</template>
		
		<template v-if="'order' in value">
			{{' '}}
			<mysqlOrder :noSpace=true></mysqlOrder>
		</template>
		
		<template v-if="'limit' in value">
			<font color=blue> limit </font>
			<mysqlLeaf :name="node_name('limit')" :value=value.limit :noSpace=true></mysqlLeaf>	
		</template>
		
		<template v-if="'offset' in value">
			<font color=blue> offset </font>
			<mysqlLeaf :name="node_name('offset')" :value=value.offset :noSpace=true></mysqlLeaf>	
		</template>
		
		<template v-if=!noSpace>
			{{' '}}
		</template>		
	</span>	
	
	<span v-else-if=is_logic v-for="value, i of args">
		<select v-if=i :value=func :style="`${style_select(func, 'blue')}`" @input=input_func>
			<option v-for="value of ['and', 'or']">{{value}}</option>
		</select> <mysqlExpr :name="`${node_name(func, i)}`" :value=value></mysqlExpr>
	</span>
	
	<span v-else-if="func == 'in'">
		<mysqlLeaf v-if=dtype[args[0]] :name="`${node_name(func, 0)}`" :value=args[0] :option=fieldsOpted></mysqlLeaf>
		<mysqlLeaf v-else-if=is_leaf(args[0]) :name="`${node_name(func, 0)}`" :value=args[0]></mysqlLeaf>
		<mysqlExpr v-else :name="`${node_name(func, 0)}`" :value=args[0]></mysqlExpr>
		<select :value=func :style="`${style_select(operator, 'red')}`" @input=input_relation>
			<option v-for="value of relationsOpted" :value=logic2physic(value)>{{value}}</option>
		</select> 
		<mysqlLeaf v-if=args[1].isString :name="`${node_name(func, 1)}`" :value=args[1] :noSpace=noSpace></mysqlLeaf>
		<template v-else>
			(<mysqlExpr v-else :name="`${node_name(func, 1)}`" :value=args[1] :noSpace=true></mysqlExpr>)
		</template>
	</span>

	<span v-else-if=is_relation v-for="value, i of args">
		<template v-if=i>
			<select :value=func :style="`${style_select(operator, 'red')}`" @input=input_relation @keydown=keydown_func>
				<option v-for="value of relationsOpted" :value=logic2physic(value)>{{value}}</option>
			</select>
			{{' '}}
		</template>
		<mysqlLeaf v-if=dtype[value] :name="`${node_name(func, i)}`" :value=value :option=fieldsOpted :noSpace="i && noSpace"></mysqlLeaf>
		<mysqlLeaf v-else-if=is_leaf(value) :name="`${node_name(func, i)}`" :value=value :option=enum_selections(i) :noSpace="i && noSpace"></mysqlLeaf>
		<mysqlExpr v-else :name="`${node_name(func, i)}`" :value=value :noSpace="i && noSpace"></mysqlExpr>
	</span>
	
	<span v-else-if=is_operator v-for="value, i of args">
		<select v-if=i :value=func :style="`${style_select(operator, 'red')}`" @input=input_func @keydown=keydown_func>
			<option v-for="value of operatorsOpted" :value=logic2physic(value)>{{value}}</option>
		</select>
		<mysqlLeaf v-if=dtype[value] :name="`${node_name(func, i)}`" :value=value :option=fieldsOpted :noSpace="i ? noSpace: true"></mysqlLeaf>
		<mysqlLeaf v-else-if=is_leaf(value) :name="`${node_name(func, i)}`" :value=value :noSpace="i ? noSpace: true"></mysqlLeaf>
		<mysqlExpr v-else :name="`${node_name(func, i)}`" :value=value :noSpace=noSpace></mysqlExpr>
	</span>

	<span v-else-if=is_function>
		<select :class=name :value=func :style="`${style_select(func, 'darkCyan')}`" @input=input_func @keydown=keydown_func>
			<option v-for="value of functionsOpted">{{value}}</option>
		</select>(<template v-for="value, i of args">
			<template v-if=i>, </template>
			<template v-if=is_leaf(value)>
				<mysqlLeaf v-if="i == 0 && (func == 'count' || func == 'json_valid')" :name="`${node_name(func, i)}`" :value=value :option=fieldsOpted :noSpace=true></mysqlLeaf>
				<mysqlLeaf v-else-if="i == 1 && func == 'substring_index'" :name="`${node_name(func, i)}`" :value=value :option=specialChars :noSpace=true></mysqlLeaf>
				<mysqlLeaf v-else-if="i == 2 && func.match(/regexp_like/)" :name="`${node_name(func, i)}`" :value=value :option="[...'icnmx']" :noSpace=true></mysqlLeaf>
				<mysqlLeaf v-else-if="i == 5 && func.match(/regexp_replace/)" :name="`${node_name(func, i)}`" :value=value :option="[...'icnmx']" :noSpace=true></mysqlLeaf>
				<mysqlLeaf v-else-if=dtype[value] :name="`${node_name(func, i)}`" :value=value :option=fieldsOpted :noSpace=true></mysqlLeaf>
				<mysqlLeaf v-else :name="`${node_name(func, i)}`" :value=value :noSpace=true></mysqlLeaf>			
			</template>
			<mysqlArgs v-else-if=value.isArray :name="`${node_name(func, i)}`" :value=value :noSpace=true></mysqlArgs>
			<mysqlExpr v-else :name="`${node_name(func, i)}`" :value=value :noSpace=true></mysqlExpr>
		</template>)</span>

	<mysqlGroup v-else-if=value.group></mysqlGroup>
	
	<mysqlOrder v-else-if=value.order :noSpace=noSpace></mysqlOrder>
	
	<span v-else-if=value.as v-for="value, i of args">
		<font v-if=i color=blue> as </font>
		<mysqlLeaf v-if=dtype[value] :name="`${node_name(func, i)}`" :value=value :option=fieldsOpted :noSpace=true></mysqlLeaf>
		<mysqlLeaf v-else-if=is_leaf(value) :name="`${node_name(func, i)}`" :value=value :noSpace=true></mysqlLeaf>
		<template v-else-if=value.select>
			<br><span v-html=indent_parenthesis></span>(<br><mysqlExpr v-else :name="`${node_name(func, i)}`" :value=value :noSpace=true></mysqlExpr><br><span v-html=indent_parenthesis></span>)
		</template>
		<mysqlExpr v-else :name="`${node_name(func, i)}`" :value=value :noSpace="i? false: true"></mysqlExpr>
	</span>
	
	<span v-else-if=is_prefix>
		<select :value=func :style="`${style_select(func, 'darkCyan')}`" @input=input_func @keydown=keydown_func>
			<option v-for="value of functionsOpted">{{value}}</option>
		</select> <mysqlLeaf v-if=dtype[arg] :name=node_name(func) :value=arg :option=fieldsOpted :noSpace=noSpace></mysqlLeaf>
		<mysqlLeaf v-else-if=is_leaf(arg) :name=node_name(func) :value=arg :noSpace=noSpace></mysqlLeaf>
		<mysqlDot v-else-if="databases.contains(Object.keys(arg)[0])" :name=node_name(func) :value=arg :noSpace=noSpace></mysqlDot>
		<mysqlExpr v-else :name="`${node_name(func)}`" :value=arg :noSpace=noSpace></mysqlExpr>
	</span>

	<span v-else>
		{{value}}
	</span>
</template>

<script>
console.log('import mysqlExpr.vue');

import mysqlLeaf from "./mysqlLeaf.vue"
import mysqlArgs from "./mysqlArgs.vue"
import mysqlDot from "./mysqlDot.vue"
import mysqlGroup from "./mysqlGroup.vue"
import mysqlOrder from "./mysqlOrder.vue"
import {simplify_expression, show_tables, show_full_columns, logic2physic, physic2logic, get_cmd, set_cmd, is_number, is_enum, is_string, is_json} from "../js/mysql.js"
export default {
	components: {mysqlLeaf, mysqlDot, mysqlGroup, mysqlOrder, mysqlArgs},//
	
	props : ['value', 'name', 'noSpace'],
	
	data(){
		return {};
	},

	created(){
		var {from} = this.value;
		if (from && from.isArray) {
			var [database, table] = from;
			//console.log({database, table});
			
			if (!database)
				return;
			
			if (this.$parent.func == 'as') {
				this.$data.database = database;
				this.$data.table = table;
				this.show_tables(database);
			}
		}
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
		
		tables_in_context() {
			var {from} = this.value;
			if (!from)
				return this.$parent.tables_in_context?? [];

			var tables = [];
			if (from.isArray) {
				tables.push(from.back());
			}
			else if (from.isString) {
				tables.push(from);
			}
			
			var {join_table} = this;
			if (join_table && join_table[1]) {
				var {as} = join_table[1];
				if (as) {
					tables.push(as[1]);
				}
			}
			
			return tables;
		},

		indent() {
			var indent = this.$parent.indent?? '';
			if (this.$parent.value.as) {
				indent += '&nbsp;'.repeat(4);
			}
			return indent;
		},
		
		indent_with() {
			//console.log(this.value, this.$parent.value);
			var indent = this.$parent.indent?? '';
			if (this.$parent.value.as) {
				indent += '&nbsp;'.repeat(4);
			}
			return indent;
		},
		
		indent_select() {
			//console.log(this.value, this.$parent.value);
			if (this.$parent.value.in)
				return '';

			var indent = this.$parent.indent?? '';
			if (this.$parent.value.as) {
				indent += '&nbsp;'.repeat(4);
			}
			
			return indent;
		},
		
		indent_parenthesis() {
			//console.log(this.value, this.$parent.value);
			var indent = this.$parent.indent?? '';			
			return indent;
		},
		
		option_join() {
			return ['json_table', ...this.tables];	
		},
		
		join_name() {
			return this.node_name(this.join_func);
		},
		
		join_func() {
			var {join_type} = this;
			if (join_type == 'inner')
				return `join`;
			return `${join_type}_join`;
		},
		
		join_table() {
			var {join_func, value: {from}} = this;
			if (join_func == 'inner')
				return from.join || from.inner_join;
			return from[join_func];
		},
		
		join_type: {
			get() {
				var {value: {from}} = this;
				if (from.inner_join || from.join)
					return 'inner';
				
				if (from.left_join)
					return 'left';
				
				if (from.right_join)
					return 'right';
				
				if (from.cross_join)
					return 'cross';
				
				if (from.full_join)
					return 'full';
			},
			
			set(join_type) {
				if (this.join_type == join_type)
					return;
				
				var {value, join_func} = this;
				value[`${join_type}_join`] = value[join_func];
				delete value[join_func];
			},
			
		},
		
		cmd: {
			get() {
				return get_cmd(this.value);
			},
			
			set(cmd) {
				set_cmd(this.value, this.cmd, cmd);
			}
		},
		
		specialChars() {
			var chars = ",:;.\\`~!@#$%^&*-=_+|?/][><'\"";
			return [...chars];	
		},
		
		option() {
			return [...this.tables_in_context, ...this.$parent.option];
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
		
		aggregate_functions() {
			return this.$parent.aggregate_functions;
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
			if (this.func.fullmatch(/count|regexp/))
				return ['*', 'distinct', ...Object.keys(this.dtype), ...this.textual_functions, 'if'];

			if (this.func == 'distinct' || this.func == 'not' || this.func == 'json_valid')
				return [...Object.keys(this.dtype), ...this.textual_functions];

			if (this.func == 'as' || this.is_aggregate_function(this.func) || this.function_is_textual) {
				return [...Object.keys(this.dtype), ...this.textual_functions, ...this.jsonobj_functions, 'if'];
			}
			
			return Object.keys(this.dtype);
		},
		
		operator() {
			return this.physic2logic(this.func);
		},
		
		is_numeric_relation(){
			if (this.value.eq || this.value.ne) {
				var [lhs, rhs] = this.args;
				lhs = this.is_numeric_type(lhs);
				rhs = this.is_numeric_type(rhs);
				if (lhs === false || rhs === false)
					return false;
				
				if (lhs === true || rhs === true)
					return true;
				return null;
			}
			
			return this.value.gt || this.value.lt || this.value.ge || this.value.le; 
		},
		
		is_jsonobj_relation(){
			return this.value.json_contains || this.value.json_contains_path; 
		},

		is_operator(){
			return this.is_numeric_operator || this.is_jsonobj_operator;
		},
		
		is_prefix(){
			var {value} = this;
			return value.distinct || value.separator || value.path || value.create || value.table || value.global || value.comment || value.after || value.not;
		},
		
		is_numeric_operator(){
			return this.value.add || this.value.sub || this.value.mul || this.value.div || this.value.mod || this.value.AND || this.value.XOR || this.value.right_shift || this.value.left_shift;
		},
		
		is_jsonobj_operator(){
			return this.value.json_extract || this.value.json_extract_unquote;
		},
		
		is_relation() {
			return this.is_numeric_relation || this.is_textual_relation || this.is_jsonobj_relation;
		},

		is_textual_relation(){
			if (this.value.eq || this.value.ne) {
				var [lhs, rhs] = this.args;
				return this.is_textual_type(lhs) || this.is_textual_type(rhs);
			}
			return this.value.regexp || this.value.like || this.value.regexp_binary || this.value.like_binary || this.value.not_regexp || this.value.not_like || this.value.not_regexp_binary || this.value.not_like_binary || this.value.in;
		},
		
		operatorsOpted() {
			return this.is_numeric_opeator ? this.numeric_operators: this.jsonobj_operators;
		},
		
		relationsOpted() {
			return this.is_numeric_relation ? this.numeric_relations: [...this.textual_relations, 'regexp_like', 'not regexp_like', ...this.jsonobj_relations];
		},
		
		functionsOpted() {
			if (this.function_is_numeric)
				return ['*', 'distinct', ...this.numeric_functions, 'count'];

			var option = [...this.textual_functions, ...this.jsonobj_functions];
			if (this.$parent.value.select == this.value || this.func == 'distinct' || this.func == 'count') 
				return ['*', 'distinct', ...option, 'max', 'min'];
			
			if (this.is_aggregate_function(this.func) || this.$parent.value.group) {
				option = [...this.aggregate_functions, ...option];
			}
			
			if (this.func == 'create') {
				return ['tables', 'create', 'grants', 'status', 'variables', 'global', 'databases'];
			}
			
			if (!option.contains(this.func)) {
				option.unshift(this.func);
			}
			
			if (this.func == 'rand') {
				return [...Object.keys(this.dtype), ...option];
			}

			return option;
		},
		
		is_function() {
			return this.function_is_numeric || this.function_is_textual || this.function_is_jsonobj || this.func.fullmatch(/json_table|columns|varchar|if|json_valid|rand/);
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
			return this.value.and || this.value.or; 
		},
		
		func(){
			var keys = Object.keys(this.value);
			if (keys.length)
				return keys[0];
			return '';
		},
		
		arg() {
			return this.args[0];			
		},

		args(){
			var values = Object.values(this.value);
			if (values.length) {
				if (values.length == 1) {
					var [value] = values;
					if (value.isArray)
						return value;
					return values;
				}
				
				console.log("multiple funcs detected");
			}
			
			return [];
		},
		
		dtype() {
			if (this.$data.dtype)
				return this.$data.dtype;
			return this.$parent.dtype;
		},
		
		desc() {
			if (this.$data.desc)
				return this.$data.desc;			
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
	},
	
	methods: {
		enum_selections(index) {
			if (index == 1) {
				var field = null;
				if (this.value.eq) {
					field = this.value.eq[0];
				}
				else if (this.value.ne) {
					field = this.value.ne[0];
				}
				else
					return;

				if (field in this.dtype) {
					var enums = this.dtype[field];
					if (enums.isArray)
						return enums;
				}
			}
		},

		delete(child) {
			switch (this.func) {
			case 'and':
			case 'or':
				var args = this.value[this.func];
				var index = args.indexOf(child);
				if (index >= 0) {
					args.delete(index);
				}
				break;
			case 'select':				
				var args = this.value[this.func];
				var index = args.indexOf(child);
				if (index >= 0 && args.length > 1) {
					args.delete(index);
				}
				break;
			}	
		},
		
		initialize_where() {
			var {value} = this;
			var {where} = value;
			
			if (where)
				return;
			
			if (len(this.desc)) {
				var where = {};
				
				var and = [];
				for (var {Field, Type, Key} of this.desc) {
					if (Key || is_number(Type) || is_enum(Type)) {
						and.push({eq: [Field, '']});
					}
					else if (is_string(Type)){
						and.push({regexp: [Field, '']});
					}
					else if (is_json(Type)){
						and.push({regexp: [Field, '']});	
					}
				}
				
				where.and = and;
				value.where = where;
				return where;
			}
		},
		
		component(value) {
			if (value.isString || value.isNumber)
				return 'mysqlLeaf';
			
			if (value.isArray)
				return 'mysqlArgs';
			
			return 'mysqlExpr';
		},
		
		async show_tables(database) {
			if (!database)
				return;
			
			var tables = await show_tables(database);
			this.$data.tables = tables;
			if (!tables.contains(this.$data.table))
				this.$data.table = tables[0];
			
			this.show_full_columns();
		},
		
		async show_full_columns(table){
			table ||= this.$data.table;
			Object.assign(this.$data, await show_full_columns(this.$data.database, table, this.host, this.user, this.token));
		},
		
		keydown_func(event) {
			var select = event.target;
			switch (event.key) {
			case "ArrowLeft":
				break;
			case "ArrowRight":
				event.preventDefault();
				if (event.ctrlKey) {
					var {parentElement} = select;
					var index;
					if (this.$parent.value.order && this.$parent.value.order[0] == this.value) {
						if (!this.$parent.value.order[1]) {
							this.$parent.value.order[1] = 'desc';
						}
						
						var name = this.name.replace(/\[0\]$/, '[1]');
						if (name == this.name)
							name += '[1]';
						
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[name="${name}"]`).focus();
						});
					}
					else if (this.$parent.value.select == this.value) {
						this.$parent.value.select = [this.value, deepCopy(this.value)];
						var name = this.name + '[1]';
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[class="${name}"]`).focus();
						});
					}
					else if (this.$parent.value.select.isArray && (index = this.$parent.value.select.indexOf(this.value)) >= 0) {
						var {select} = this.$parent.value;						 
						this.$parent.value.select = [...select.slice(0, index), this.value, deepCopy(this.value), ...select.slice(index + 1)];
						var name = this.name.replace(/\[\d+\]$/, `[${index + 1}]`);
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[class="${name}"]`).focus();
						});
					}
					else {
						var func = Object.keys(this.$parent.value)[0];
						if (func.fullmatch(this.textual_function_regexp) || func.fullmatch(this.jsonobj_function_regexp)) {
							if (this.$parent.value[func] == this.value) {
								if (func == 'group_concat') {
									this.$parent.value[func] = [[this.$parent.value[func], {order: this.PRI}]];
									var name = this.name
									name += '[0][1]';
									
									this.$parent.$nextTick(()=>{
										parentElement.querySelector(`select[name="${name}"]`).focus();
									});
								}
								else {
									this.$parent.value[func] = [this.$parent.value[func], deepCopy(this.$parent.value[func])];
									var name = this.name.replace(/\[0\]$/, '[1]');
									if (name == this.name)
										name += '[1]';
									
									this.$parent.$nextTick(()=>{
										parentElement.querySelector(`select[class="${name}"]`).focus();
									});
								}
							}
							else {
								var index = this.$parent.value[func].indexOf(this.value);
								if (index >= 0) {
									var name = this.name.replace(eval(`/\\[${index}\\]$/`), `[${index + 1}]`);
									if (this.$parent.value[func][index + 1]) {
										if (this.$parent.value[func][index + 1].isString) {
											this.$parent.$nextTick(()=>{
												parentElement.querySelector(`input[name="${name}"]`).focus();
											});
										}
										else {
											this.$parent.$nextTick(()=>{
												parentElement.querySelector(`select[class="${name}"]`).focus();
											});
										}
									}
									else {
										this.$parent.value[func][index + 1] = deepCopy(this.$parent.value[func][index]);
										this.$parent.$nextTick(()=>{
											parentElement.querySelector(`select[class="${name}"]`).focus();
										});
									}
								}
							}
						}
					}
				}
				else {
				}
				
				break;
				
			case "ArrowUp":
				break;
				
			case "ArrowDown":
				if (!event.ctrlKey) {
					break;
				}
				
				var {parentElement} = select;
				var func = Object.keys(this.$parent.value)[0];
				var hit = false;
				if (this.$parent.value[func] == this.value) {
					this.$parent.value[func] = {concat: this.$parent.value[func]};
					hit = true;
				}
				else {
					var index = this.$parent.value[func].indexOf(this.value);
					if (index >= 0) {
						this.$parent.value[func][index] = {concat: this.$parent.value[func][index]};
						hit = true;
					}
				}
				
				if (hit) {
					var {name} = this;
					name += '[concat]';
					this.$parent.$nextTick(()=>{
						var element = parentElement.querySelector(`select[class="${name}"]`) || parentElement.querySelector(`select[class="${name}[0]"]`);
						element.focus();
					});
				}
				
				break;
				
			case 'F2':
				if (this.$parent.value.select === this.value) {
					this.$parent.value.select = {as: [this.value, this.PRI]};
					console.log(this.$parent.value.select);
					
					var {parentElement} = select;
					var name = this.name + '[as][1]';
					this.$parent.$nextTick(()=>{
						parentElement.querySelector(`select[name="${name}"]`).focus();
					});
				}
				break;
			case 'Insert':
				var {parentElement} = select;
				var func = Object.keys(this.$parent.value)[0];
				var hit = false;
				if (func.fullmatch(this.textual_function_regexp) || func.fullmatch(this.jsonobj_function_regexp)) {
					if (this.$parent.value[func] == this.value) {
						this.$parent.value[func] = '';
						hit = true;
					}
					else {
						var index = this.$parent.value[func].indexOf(this.value);
						if (index >= 0) {
							this.$parent.value[func][index] = '';
							hit = true;
						}
					}
				}
				else if (func == 'eq') {
					this.$parent.value.eq[1] = '';
					hit = true;
				}
				
				if (hit) {
					var {name} = this;
					this.$parent.$nextTick(()=>{
						parentElement.querySelector(`input[name="${name}"]`).focus();
					});
				}
				
				break;

			case 'Delete':
				this.$parent.delete(this.value);
				break;
			default:
				break;
			}
		},
		
		keydown_cmd(event) {
			var select = event.target;
			switch (event.key) {
			case "ArrowDown":
				if (!event.ctrlKey) {
					break;
				}
				
				var {parentElement} = select;
				var hit = false;
				if (this.$parent.value == this.value) {
					var table = '_t';
					var {value} = this;
					value = deepCopy(value);
					delete value.transform;
					if (!value.limit)
						delete value.limit;
					
					if (!value.offset)
						delete value.offset;
					
					if (!value.order)
						delete value.order;
					
					simplify_expression(value);
					
					this.value.with = {as: [table, value]};
					this.value.select = '*';
					this.value.from = table;
					
					delete this.value.group;
					delete this.value.having;
					delete this.value.where;
					this.value.limit = '';
					this.value.offset = '';
					this.value.order = '';

					delete this.value.inner_join;				
					delete this.value.left_join;				
					delete this.value.right_join;				
					delete this.value.cross_join;				
					delete this.value.full_join;

					hit = true;
				}
				
				if (hit) {
				}
				
				break;
				
			default:
				break;
			}
		},

		physic2logic(func) {
			return physic2logic[func]?? func;
		},
		
		logic2physic(func) {
			return logic2physic[func]?? func;
		},
		
		input_func(event) {
			var {_value, value} = event.target;
			_value = this.logic2physic(_value);
			if (_value == value)
				return;
			var {name} = this;
			
			console.log({_value, value, name});
			
			if (value in this.dtype) {
				for (var key in this.$parent.value) {
					if (this.$parent.value[key] === this.value) {
						this.$parent.value[key] = value;
						return;
					}
				}
			}

			this.value[value] = this.value[_value];
			delete this.value[_value];
			
			if (_value == 'group_concat') {
				if (this.value[value].isArray)
					this.value[value] = this.value[value][0];
			}

			switch (value) {
			case 'regexp_like':
				var args = this.value[value];
				if (!args.isArray) {
					args = [args, ''];
					this.value[value] = args;
				}
				
				if (!args[2])
					args[2] = 'c';
				break;
				
			case 'substring':
				var args = this.value[value];
				if (!args.isArray) {
					args = [args, ''];
					this.value[value] = args;
				}
				
				if (!args[1])
					args[1] = '1';
				
				break;
				
			case 'substring_index':
				var args = this.value[value];
				if (!args.isArray) {
					args = [args, ''];
					this.value[value] = args;
				}
				
				if (!args[1])
					args[1] = ',';
				
				if (args[2]) {
					if (!args[2].isdigit()) {
						args[2] = '1';
					}
				}
				else {
					args[2] = '1';
				}
				break;

			case 'regexp_replace':
				var args = this.value[value];
				if (!args.isArray) {
					args = [args, ''];
					this.value[value] = args;
				}

				if (!args[1]) {
					args[1] = '';
				}

				if (!args[2]) {
					args[2] = '';
				}
				break;

			case 'json_remove':
				var args = this.value[value];
				if (!args.isArray) {
					args = [args, ''];
					this.value[value] = args;
				}

				if (!args[1]) {
					args[1] = '';
				}

				if (args.length > 2) {
					args.resize(2);
				}
				break;

			case 'sum':
				if (this.value[value].isArray) {
					this.value[value] = this.value[value][0];
				}
				break;
				
			case '*':
				var {select} = this.$parent.value;
				var index;
				if (select == this.value) {
					this.$parent.value.select = value;
				}
				else if (select.isArray && (index = select.indexOf(this.value)) >= 0){
					this.$parent.value.select[index] = value;
				}

				break;

			default:
				break;
			}
		},
		
		input_relation(event) {
			var {_value, value} = event.target;
			_value = this.logic2physic(_value);
			if (_value == value)
				return;
			var {name} = this;
			
			console.log({_value, value, name});
			
			this.value[value] = this.value[_value];
			delete this.value[_value];
			
			switch (value) {
			case 'in':
				var args = this.value[value];
				args[1] = {from: '_t', select: args[0]};
				break;
				
			case '*':
				if (this.$parent.value.select == this.value) {
					this.$parent.value.select = value;					
				}
				break;

			case 'not':
				var args = this.value[value];
				args.delete(1);
				break;

			default:
				break;
			}
		},

		is_textual_type(value) {
			var type = this.is_numeric_type(value);
			if (type == null)
				return type;
			return !type;
		},
		
		is_numeric_type(value) {
			if (value.isString) {
				if (this.dtype[value]) {
					if (this.dtype[value] == 'string' || this.dtype[value] == 'json' || this.dtype[value].isArray)
						return false;
				}
				
				if (value.isdigit())
					return true;
				if (!value)
					return null;
				return true;
			}
			
			var [func] = Object.keys(value);
			switch (func) {
			case 'count':
			case 'sum':
			case 'agv':
			case 'max':
			case 'min':
			case 'std':
			case 'stddev_samp':
			case 'variance':
			case 'var_samp':
			case 'var_pop':
			case 'bit_and':
			case 'bit_or':
			case 'bit_xor':
				return true;
				
			case 'group_concat':
			case 'json_arrayagg':
			case 'json_objectagg':
			case 'json_remove':
				return false;
				
			case 'add':
			case 'sub':
			case 'mul':
			case 'div':
			case 'mod':
			case 'AND':
			case 'XOR':
			case 'right_shift':
			case 'left_shift':				
				return true;
				
			case 'substring':
			case 'substring_index':
			case 'regexp_substr':
			case 'regexp_replace':
				return false;
				
			case 'length':
			case 'char_length':
			case 'json_length':
				return true;
				
			case 'json_extract'://->
			case 'json_unquote_extract'://->>
				return null;

			default:
				console.log('unknown function', func);
				return null;
			}
		},

		node_name(name, i) {
			if (this.name) {
				if (i == null)
					return `${this.name}[${name}]`;
					
				if (i == 0 && this.args.length == 1 && (!this.args[0] || !this.args[0].isArray)) {
					return `${this.name}[${name}]`;
				}
				
				return `${this.name}[${name}][${i}]`;
			}	

			if (i == null)
				return name;
			
			if (i == 0 && this.args.length == 1 && (!this.args[0] || !this.args[0].isArray)) {
				return name;
			}
			
			return `${name}[${i}]`;;
		},
		
		getitem(attr, index) {
			var value = this.$parent.value.select[attr];
			if (value.isString) {
				if (index)
					return;
				return value;
			}
			
			return value[index];
		},

		extract_funcs_and_args(select) {
			if (!select) {
				var {select} = this.$parent.value;
				if (select)
					return this.extract_funcs_and_args(select);
				return {};
			}
			
			var funcs = [];
			var [[func, args]] = Object.entries(select);
			funcs.push(func);
			
			if (args.isArray || args.isString)
				return {funcs, args};
			
			var {funcs: _funcs, args} = this.extract_funcs_and_args(args);
			
			funcs.push(..._funcs);
			return {funcs, args};
		},
	},
};
</script>

<style>
select.cmd, select.join_type{
	color: blue;
}

</style>
