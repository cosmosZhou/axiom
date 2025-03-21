<template>
	<span class=set>
		<table border=0 cellpadding=0 cellspacing=0>
			<tr>
				<td rowspan=2>
					<select class=cmd v-model=$parent.cmd :style=style_select($parent.cmd)>
						<option v-for="value of cmds" :value=value>{{value}}</option>
					</select>
				</td>
				
				<td rowspan=2>
					&nbsp;
					<select class=password name=set[eq][0] :value=value.set.eq[0]>
						<option value=password>password</option>
					</select>
				</td>
				
				<td rowspan=2 color=red>&nbsp;=&nbsp;</td>
				
				<td>
					<input v-focus type=password v-model=password :size=size_input title="reset your password" @keydown=keydown />
				</td>
			</tr>
			<tr>
				<td>
					<input type=password name=set[eq][1] v-model=password_confirmed :size=size_input title="comfirm your password" @blur=blur_input @keydown=keydown />
				</td>
			</tr>
		</table>
		
		<p v-if=error>the password confirmed is not the same as the first input, resetting to ''</p>
	</span>
</template>

<script>
console.log('import mysqlSet.vue');
//set password = '123456';

export default {
	components: {},
	
	props : ['kwargs'],
	
	data() {
		var {$data} = this.$parent;
		$data.password_confirmed = '';
		$data.error = false;
		return $data;
	},

	created() {
		var {data} = this.$parent.$parent;
		if (data && data.isArray)
			data.clear();
		
		if (this.$parent.sql && !this.$parent.sql.match(/^set /))
			setAttribute(this, 'sql', '');
	},
	
	computed: {
		password: {
			get() {
				return this.value.set.eq[1]?? '';
			},
			
			set(password) {
				this.value.set.eq[1] = password;
			},
		},
		
		size_input() {
			return Math.max(8, this.password.length, this.password_confirmed.length);
		},
		
		change_table() {
			return this.$parent.change_table;
		},
		
		change_database() {
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

		where_dict() {
			return this.$parent.where_dict;
		},

		value() {
			return this.kwargs;
		},
		
		autoLabellingType() {
			var {transform} = this.kwargs;

			var labellingType = {};
			if (transform) {
				for (var field in transform) {
					if (transform[field] == 'infix')
						labellingType[field] = 'syntax';
				}
			}
			
			var {style} = this;
			for (var field in style) {
				labellingType[field] = 'entity';
			}
			
			return labellingType;
		},
		
		fieldsForLabelling() {
			return Object.keys(this.autoLabellingType);
		},
		
		change_input() {
			return this.$parent.change_input;
		},
		
		style_select_table() {
			return this.$parent.style_select_table;
		},
		
		style_select() {
			return this.$parent.style_select;
		},
		
		style_input() {
			return this.$parent.style_input;
		},
		
		input_kwargs() {
			return this.$parent.input_kwargs;
		},
		
		PRI() {
			return this.$parent.PRI;
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
	
	mounted() {
	},

	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	el.focus();
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
