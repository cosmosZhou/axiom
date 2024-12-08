<template>
	<span class=select>
		<mysqlExpr :name="''" :value=value></mysqlExpr>
		<br><br>
		
		<select v-model=actionToGet :style=style_select(actionToGet)>
			<option v-for="value of ['browse', 'download', 'backup']" :value=value>{{value}}</option>
		</select>
		<a :href=href_select title="click here to get the data via url" target=_blank>
			data from url
		</a>&nbsp;
		<label>sample =  
			<input type=text name=sample v-model=sample :size="sample? sample.toString().length + 2: 5" />
		</label>
	</span>
</template>

<script>
//modifier: icnmx
//https://dev.mysql.com/doc/refman/8.0/en/regexp.html#function_regexp-like
//detect duplicates:
//http://localhost/label/query.php?user=user&sql=select group_concat(json_quote(pn)) from corpus.markush group by text having count(*) > 1 limit 40
/*
//remove duplicates:
with _t as (
	with _t as (
		select json_remove(json_unquote(concat('[', group_concat(json_quote(pn) order by training), ']')), '$[0]') as pns from markush group by text having count(*) > 1
	)
	select pn from _t cross join json_table(pns, '$[*]' columns(pn varchar(36) path '$')) as _s
)
delete from markush where pn in (select pn from _t);
//url representation:
//http://localhost/label/query.php?user=user&sql=with _t as (with _t as (select json_remove(json_unquote(concat('[', group_concat(json_quote(pn)), ']')), '$[0]') as pn from corpus.markush group by text having count(*) > 1) select _s.pn from _t cross join json_table(pn, '$[*]' columns(pn varchar(36) path '$')) as _s) select pn, text from corpus.markush where pn in (select pn from _t) limit 1000

with _t as (
	with _t as (
		with _t as (
			select json_remove(json_unquote(concat('[', group_concat(json_quote(pn) order by training), ']')), '$[0]') as pns from markush group by text having count(*) > 1
		)
	   	select pn from _t cross join json_table(pns, '$[*]' columns(pn varchar(36) path '$')) as _s
	)
	select distinct text from markush where pn in (select pn from _t) and training = 0
)
select group_concat(training), sum(if (training = 0, 1, 0)), text from markush where text in (select text from _t) group by text;

// url representation:
// http://localhost/label/query.php?user=user&sql=with _t as (with _t as (with _t as (select json_remove(json_unquote(concat('[', group_concat(json_quote(pn) order by(training)), ']')), '$[0]') as pn from corpus.markush group by text having count(*) > 1) select _s.pn from _t cross join json_table(pn, '$[*]' columns(pn varchar(36) path '$')) as _s) select distinct text from corpus.markush where training = 0 and pn in (select pn from _t)) select group_concat(training order by(training)), sum(if(training = 0, 1, 0)), text from corpus.markush where text in (select text from _t) group by text limit 1000
// unnest json array:
with _t as (
    with _t as (
        with _t as (
            select json_unquote(text) as texts, id from sentiment where training in (0, 1) limit 1000000
        )
        select _s.text as text, id from _t join sentiment using (id) cross join json_table(texts, '$[*]' columns(text text path '$')) as _s
	)
    select id from _t where text not in (select text->'$[0]' from sentiment where training = 2)
)
select * from corpus.sentiment where id in (select * from _t) limit 1 offset 1
// url representation:
*/
 
console.log('import mysqlSelect.vue');
import mysqlExpr from "./mysqlExpr.vue"
import mysqlDot from "./mysqlDot.vue"

import {get_db_table, piece_together} from "../js/mysql.js"

export default {
	components: {mysqlExpr, mysqlDot},
	
	props : ['kwargs'],
	
	data(){
		var {$data} = this.$parent;
		$data.actionToGet = 'browse';
		$data.name = '';
		return $data;
	},

	created(){
		var {kwargs} = this;
		var {regexp} = kwargs;
		if (regexp) {
			kwargs[this.table] = regexp[this.table];
			kwargs.operator[this.table] = 'regexp';
		}
		
		if (!kwargs.where) {
			kwargs.where = {};
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
		
		sample: {
			get() {
				return this.$parent.sample;
			},
			
			set(sample) {
				setAttribute(this, 'sample', sample);
			},
		},
		
		sql() {
			var kwargs = {...this.kwargs};
			var {transform: __transform__} = kwargs;
			delete kwargs.transform;
			
			if (!kwargs.limit)
				kwargs.limit = 40;
			
			if (!kwargs.select)
				kwargs.select = '*';
			
			return this.process_statement(kwargs, {...this.dtype, __transform__});
		},
		
		parse_expression() {
			return this.$parent.parse_expression;
		},
		
		tables() {
			return this.$parent.tables;
		},
		
		databases() {
			return this.$parent.databases;
		},

		is_leaf() {
			return this.$parent.is_leaf;
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
		
		numeric_function_regexp() {
			return this.$parent.numeric_function_regexp;
		},
		
		jsonobj_function_regexp() {
			return this.$parent.jsonobj_function_regexp;
		},
		
		textual_function_regexp() {
			return this.$parent.textual_function_regexp;
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
		
		numericFields() {
			return this.$parent.numericFields;
		},

		textualFields() {
			return this.$parent.textualFields;
		},
		
		where_dict() {
			return this.$parent.where_dict;
		},
		
		option() {
			return this.$parent.option;
		},
		
		value(){
			return this.kwargs;
		},
		
		PRI() {
			return this.$parent.PRI;
		},
		
		database() {
			return this.$parent.database;
		},
		
		table() {
			return this.$parent.table;
		},
		
		href_select() {
			var {sample, host, user, transform, kwargs} = this;

			if (this.actionToGet == 'backup') {
				var kwargs = {user, table: this.table, vue: 'backup'};
				if (host && host != 'localhost')
					kwargs.host = host;
				return 'index.php?' + get_url(kwargs);
			}
			
			var url = [];
			url.push(`user=${user}`);
			if (host && host != 'localhost')
				url.push(`host=${host}`);

			url.push(...piece_together(kwargs));
			if (sample)
				url.push(`sample=${sample}`);
			
			if (this.actionToGet == 'download')
				url.push(`download=true`);
			
			for (var Field in transform) {
				url.push(`transform[${Field}]=${transform[Field]}`);
			}
			
			return 'query.php?' + url.join('&');
		},
		
		change_table(){
			return this.$parent.change_table;
		},
		
		change_database(){
			return this.$parent.change_database;
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
		
		style_select() {
			return this.$parent.style_select;
		},
		
		style_entity() {
			return this.$parent.style_entity;
		},
	},
	
	methods: {
		process_select(kwargs) {
		    var {select} = kwargs;
		    
		    var sql = "select ";
		    if (select) {
		        if (select.isArray) {
		        	sql += select.map(cond => this.parse_expression(cond)).join(", ");
		        }
		        else if (select.isString){
		            sql += select;
		        }
		        else {
		        	sql += this.parse_expression(select);
		        }
		    } else {
		        sql += "*";
		    }
		    
		    sql += " ";
		    return sql;
		},
		
		process_statement(kwargs, Field2Type) {
		    var sql = this.process_select(kwargs);
		    
		    var {from} = kwargs;
		    if (from.from) {
		        var statement = this.process_statement(kwargs.from, Field2Type);
		        sql += `from (${statement}) as _t`;
		    }
		    else if (from.isString) {
		        sql += `from ${from} `;
		    }
		    else {
		        var {database, table} = get_db_table(from);
		        sql += `from ${database}.${table} `;
		    }
		    
		    var condition = this.parse_expression(kwargs.where?? {}, Field2Type);
		    
		    if (condition) {
		        sql += `where ${condition} `;
		    }
		    
		    var {group} = kwargs;
		    if (group) {
		        sql += `group by ${group} `;
		        var {having} = kwargs;
		        if (having) {
		            var having_condition = this.parse_expression(having, Field2Type);
		            if (having_condition) {
		                sql += `having ${having_condition} `;
		            }
		        }
		    } else{
		        var {order} = kwargs;
		        if (order) {
		            sql += `order by ${order} `;
		        }
		    }
		    
		    var {limit, offset} = kwargs;
		    if (limit)
		        sql += `limit ${limit} `;
		    
		    if (offset)
		        sql += `offset ${offset} `;
		        
		   return sql;
		},
		
		extract_funcs_and_args(select) {
			if (!select) {
				var {select} = this.kwargs;
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

		json_decode_by_field_to_type(data) {
			var {as} = this.value.select;
			if (as) {
				var [asValue, Field] = this.value.select.as;
				if (asValue.json_object) {
					this.$parent.json_decode(data, Field);
				}
			}
			
			this.$parent.json_decode_by_field_to_type(data);
		},
	},
	
	mounted() {
	},
}
</script>