<template>
	<span class=delete>
		<mysqlExpr :name="''" :value=value></mysqlExpr>
		<br><br>

		<select v-model=actionToGet :style="style_select(actionToGet)">
			<option v-for="value of ['browse', 'download', 'backup']" :value=value>{{value}}</option>
		</select>
		<a :href=href_delete title="click here to get the data via url" target=_blank>
			data from url
		</a>&nbsp;
		<label>sample =
			<input type=text name=sample v-model=sample :size="sample? sample.toString().length + 2: 5" />
		</label>
		<button type=button class=transparent @click=click_execute><u>execute</u></button>
		<input type=checkbox v-model=execute />&nbsp;&nbsp;
		<button type=button class=transparent @click=click_repeat><u>repeat</u></button>
		<input type=checkbox v-model=repeat />

		<input type=hidden name=delete value=true />
	</span>
</template>

<script>
import mysqlDot from "./mysqlDot.vue"
import mysqlExpr from "./mysqlExpr.vue"
console.log('import mysqlDelete.vue');

import {piece_together} from "../js/mysql.js"

export default {
	components: {mysqlDot, mysqlExpr},

	props : ['kwargs'],

	data() {
		var {$data} = this.$parent;
		return {
			...$data,
			actionToGet: 'browse',
		};
	},

	created() {
		this.$data.execute = getParameterByName('execute');
		this.$data.repeat = getParameterByName('repeat');
	},

	computed: {
		change_table() {
			return this.$parent.change_table;
		},

		change_database() {
			return this.$parent.change_database;
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


		option() {
			return this.$parent.option;
		},

		PRI() {
			return this.$parent.PRI;
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

		style_select() {
			return this.$parent.style_select;
		},

		value() {
			return this.kwargs;
		},

		change_table() {
			return this.$parent.change_table;
		},

		change_input() {
			return this.$parent.change_input;
		},

		style_select_table() {
			return this.$parent.style_select_table;
		},

		style_input() {
			return this.$parent.style_input;
		},

		input_kwargs() {
			return this.$parent.input_kwargs;
		},

		databases() {
			return this.$parent.databases;
		},

		tables() {
			return this.$parent.tables;
		},

		sample: {
			get() {
				return this.$parent.sample;
			},

			set(sample) {
				setAttribute(this, 'sample', sample);
			},
		},

		href_delete() {
			var kwargs = {...this.kwargs};
			delete kwargs.delete;
			var url = piece_together(kwargs);
			var {sample, host} = this;
			if (sample)
				url.push(`sample=${sample}`);

			if (host && host != 'localhost')
				url.push(`host=${host}`);

			url.push(`delete=true`);
			if (this.execute)
				url.push("execute=true");

			if (this.repeat)
				url.push("repeat=true");

			return 'query.php?' + url.join('&');
		},
	},

	methods: {
		click_execute(event) {
			this.execute = !this.execute;
			event.preventDefault();
		},

		click_repeat(event) {
			this.repeat = !this.repeat;
			event.preventDefault();
		},
	},

	directives: {
	},
}
</script>

<style scoped>
</style>