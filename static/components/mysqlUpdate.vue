<template>
	<span class=update>
		<template v-if=with_func>
			<font color=blue>{{with_func}} </font>
			<mysqlExpr v-if=with_value.isArray v-for="value, i of with_value" :name="`${with_func}[${i}]`" :value=value></mysqlExpr>
			<mysqlExpr :name="'with'" :value=with_value></mysqlExpr><br>
		</template>
		<select class=cmd v-model=$parent.cmd>
			<option v-for="value of cmds" :value=value>{{value}}</option>
		</select>{{' '}} 
		<template v-if=join_type>
			<template v-if=join_table[0].join>
				<mysqlLeaf :name="'update[join][0]'" :value=join_table[0].join[0]></mysqlLeaf>
				<font color=blue> join </font>
				<mysqlLeaf :name="'update[join][1]'" :value=join_table[0].join[1]></mysqlLeaf>
				<template v-if=join_table[0].using>
					<font color=blue> using </font>
					(<mysqlLeaf :name="'update[using]'" :value=join_table[0].using :option=option_join></mysqlLeaf>)
				</template>
				<mysqlExpr v-else-if=join_table[0].on :name="'update[on]'" :value="join_table[0].on"></mysqlExpr>
			</template>
			<mysqlDot v-else :name="'update'" :value=join_table[0]></mysqlDot>
		
			<select class=join_type v-model=join_type>
				<option v-for="value of ['inner', 'cross', 'left', 'right', 'full']" :value=value>{{value}}</option>
			</select><font color=blue> join </font>
			<mysqlLeaf v-if="is_leaf(join_table[1])" :name="`update[${join_func}]`" :value=join_table[1] :option=option_join></mysqlLeaf>
			<mysqlExpr v-else :name="`update[${join_func}]`" :value=join_table[1]></mysqlExpr>
		</template>
		<mysqlDot v-else :name="'update'" :value=value.update></mysqlDot>
		<font color=blue> set </font>
		<template v-if="value.set.isArray" v-for="value, index of value.set">
			<template v-if=index>, </template>
			<mysqlExpr :name="`set[${index}]`" :value=value :noSpace=true></mysqlExpr>
		</template>
		<mysqlExpr v-else :name="'set'" :value=value.set></mysqlExpr>
		<template v-if="value.where && Object.keys(value.where).length">
			<font color=blue> where </font>
			<mysqlExpr :name="'where'" :value=value.where></mysqlExpr>
		</template>

		<template v-if="'order' in value">
			{{' '}}
			<mysqlOrder :noSpace=true></mysqlOrder>
		</template>
		
		<template v-if="'limit' in value">
			<font color=blue> limit </font>
			<mysqlLeaf :name="'limit'" :value=value.limit :noSpace=true></mysqlLeaf>	
		</template>
		
		<template v-if="'offset' in value">
			<font color=blue> offset </font>
			<mysqlLeaf :name="'offset'" :value=value.offset :noSpace=true></mysqlLeaf>	
		</template>
		
		<br><br>
		<a :href=href_select title="click here to view the old data before transformation" target=oldData>view old data</a>
		&nbsp;&nbsp;&nbsp;&nbsp;<a :href=href_update title="batch execute" target=execute>batch execute</a>&nbsp;
		<label>sample =  
			<input type=text name=sample v-model=sample :size="sample? sample.toString().length + 2: 5">
		</label>
		<button type=button class=transparent @click=click_execute><u>execute</u></button>
		<input type=checkbox v-model=execute />&nbsp;&nbsp;
		<button type=button class=transparent @click=click_repeat><u>repeat</u></button>
		<input type=checkbox v-model=repeat />
		
		<template v-if=fieldsForLabelling.length>
			&nbsp;&nbsp;&nbsp;
			<select v-model=fieldForLabelling>
				<option v-for="field of fieldsForLabelling" :value=field>{{field}}</option>
			</select>
			<button type=button class=transparent @click=click_labelling :title="`labelling ${fieldForLabelling} semi-automatically`"><u>auto-labelling</u></button>
		</template> 
		
	</span>
</template>

<script>
import {piece_together} from "../js/mysql.js"
import mysqlLeaf from "./mysqlLeaf.vue"
import mysqlExpr from "./mysqlExpr.vue"
import mysqlDot from "./mysqlDot.vue"
import mysqlGroup from "./mysqlGroup.vue"
import mysqlOrder from "./mysqlOrder.vue"
console.log('import mysqlUpdate.vue');

export default {
	components: {mysqlLeaf, mysqlDot, mysqlExpr, mysqlGroup, mysqlOrder},
	
	props : ['table', 'limit', 'offset', 'kwargs'],
	
	data() {
		var {$data} = this.$parent;
		$data.fieldForLabelling = null;
		return $data;
	},

	created(){
		var {value} = this;
		var {set} = value;
		if (set.eq && !set.eq[0]) {
			var {functor, setter} = this;
			this.fieldForLabelling = setter;
			console.log({setter, functor});
		}
		
		if (!value.where)
			value.where = {};
	},
	
	computed: {
		repeat: {
			get(){
				var {kwargs} = this.kwargs;
				if (kwargs)
					return kwargs.execute == 'repeat';
				return false;
			},

			set(repeat){
				var {kwargs} = this.kwargs;
				if (kwargs) {
					if (repeat)
						kwargs.execute = 'repeat';
					else if (kwargs.execute == 'repeat')
						kwargs.execute = true;
				}
				else {
					if (repeat)
						this.kwargs.kwargs = {execute : 'repeat'};
				}
			},
		},

		execute: {
			get(){
				var {kwargs} = this.kwargs;
				if (kwargs)
					return kwargs.execute? true : false;
				return false;
			},

			set(execute){
				var {kwargs} = this.kwargs;
				if (kwargs) {
					if (execute) {
						if (!kwargs.execute)
							kwargs.execute = true;
					}
					else {
						if (kwargs.execute)
							kwargs.execute = false;
					}
				}
				else {
					if (execute)
						this.kwargs.kwargs = {execute : true};
				}
			},
		},

		option() {
			return this.$parent.option;
		},

		with_func() {
			var {value} = this;
			if (value.with)
				return 'with';
			if (value.with_recursive)
				return 'with recursive';
		},

		with_value() {
			var {value} = this;
			if (value.with)
				return value.with;
			if (value.with_recursive)
				return value.with_recursive;
		},

		join_type() {
			var {value: {update}} = this;
			if (update.inner_join || update.join)
				return 'inner';
			
			if (update.left_join)
				return 'left';
			
			if (update.right_join)
				return 'right';
			
			if (update.cross_join)
				return 'cross';
			
			if (update.full_join)
				return 'full';
		},

		join_table() {
			var {join_func, value: {update}} = this;
			if (join_func == 'inner')
				return update.join || update.inner_join;
			return update[join_func];
		},

		join_func() {
			var {join_type} = this;
			if (join_type == 'inner')
				return `join`;
			return `${join_type}_join`;
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

		is_numeric_function() {
			return this.$parent.is_numeric_function;
		},
		
		is_aggregate_function() {
			return this.$parent.is_aggregate_function;
		},

		is_textual_function() {
			return this.$parent.is_textual_function;
		},

		is_jsonobj_function() {
			return this.$parent.is_jsonobj_function;
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
		
		order: {
			get() {
				return this.$parent.order;
			},
			
			set(order) {
				this.$parent.order = order;
			}
		},
		
		group: {
			get() {
				return this.$parent.group;
			},
			
			set(order) {
				this.$parent.group = group;
			}
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
		
		href_select() {
			var {sample, host, transform, kwargs} = this;
			var url = [];
			if (host && host != 'localhost')
				url.push(`host=${host}`);
			
			kwargs = {...kwargs};
			kwargs.from = kwargs.update;
			delete kwargs.update;
			var {set, where} = kwargs;
			if (!where) {
				var and = [];
			}
			else if (where.and) {
				var {and} = where;
				and = [...and];
			}
			else {
				var and = [where];
			}

			delete kwargs.set;
			if (set.isArray) {
				
			}
			else {
				var {functor, setter, old, new: $new} = this;
				switch (functor) {
				case 'regexp_replace':
					var regexp = [setter, old];
					and.push({regexp});
				}
			}
			
			kwargs.where = {and};
			url.push(...piece_together(kwargs));
			if (sample)
				url.push(`sample=${sample}`);
			
			for (var Field in transform) {
				url.push(`transform[${Field}]=${transform[Field]}`);
			}
			
			return 'query.php?' + url.join('&');
		},

		href_update() {
			var {sample, host, transform, kwargs} = this;
			var url = [];
			if (host && host != 'localhost')
				url.push(`host=${host}`);
			
			url.push(...piece_together(kwargs));
			if (sample)
				url.push(`sample=${sample}`);
			
			for (var Field in transform) {
				url.push(`transform[${Field}]=${transform[Field]}`);
			}
			if (this.execute) {
				if (this.repeat)
					url.push("kwargs[execute]=repeat");
				else
					url.push("kwargs[execute]=true");
			}
			return 'query.php?' + url.join('&');
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

		functor: {
			get() {
				var {set} = this.kwargs;
				if (set) {
					var [lhs, rhs] = set.eq;
					if (lhs) {
						if (rhs){
							if (rhs.isString)
								return '';
							return Object.keys(rhs)[0];
						}
						return '';
					}
				}
				
				var where_dict = this.where_dict(this.value.where, true);
				var args = [this.setter, '', ''];
				if (where_dict[this.setter]) {
					args[1] = where_dict[this.setter].regexp[1];
				}
				
				set.eq = [this.setter, {regexp_replace: args}];
				return 'regexp_replace';
			},
			
			set(functor){
				if (this.functor == functor) {
					return;
				}
				
				var {set} = this.kwargs;
				if (set) {
					var [lhs, rhs] = set.eq;
					if (rhs.isString) {
						rhs = {};
						rhs[functor] = [lhs, set.eq[1]];
						set.eq[1] = rhs;
					}
					else {
						rhs[functor] = rhs[this.functor];
						delete rhs[this.functor];
					}
				}
				else {
					set = {};
					this.kwargs.set = set;
					var rhs = {};
					rhs[functor] = [this.setter, ''];
					set.eq = [this.setter, rhs];
				}
			},
		},
		
		old: {
			get() {
				var {set: {eq: [lhs, rhs]}} = this.kwargs;
				var {functor} = this;
				if (functor) {
					switch (functor) {
					case 'regexp_replace':
						return rhs[functor][1];
					}
				}
			},

			set(old){
			},
		},
		
		new: {
			get() {
				var {set: {eq: [lhs, rhs]}} = this.kwargs;
				var {functor} = this;
				if (functor) {
					switch (functor) {
					case 'regexp_replace':
						return rhs[functor][2];
					}
				}
			},
			
			set(val){
			},
		},
		
		setter: {
			get() {
				var {set} = this.kwargs;
				if (set) {
					if (set.isArray) {
						return set.map(cond => cond.eq[0]);
					}
					else {
						if (!set.eq[0])
							set.eq[0] = this.get_setter();
						return set.eq[0];
					}
				}
			},
			
			set(setter) {
				var {set} = this.kwargs;
				if (set) {
					if (set.isArray) {
						return;
					}
					else {
						set.eq[0] = setter;
					}
				}
				else {
					this.kwargs.set = {eq: [setter, '']};
				}
			},
		},
	},
	
	methods: {
		delete(child) {
			var {set} = this.value;
			if (set.isArray) {
				var index = set.indexOf(child);
				if (index >= 0) {
					set.delete(index);
					if (set.length == 1) {
						[this.value.set] = set;
					}
				}
			}
		},

		get_setter() {
			var {kwargs, transform} = this;
			var where_dict = this.where_dict(this.kwargs.where?? {}, true);
			var fieldsToSet = [];
			for (var Field in this.dtype) {
				if (Field == this.PRI)
					continue;

				if (where_dict[Field])
					fieldsToSet.push(Field);
			}

			if (fieldsToSet.length == 1)
				return fieldsToSet[0];
			
			if (fieldsToSet.length == 0) {
				return 'text';
			}
			
			for (var field of fieldsToSet) {
				if (field in transform)
					return field;
			}

			if (this.style) {
				for (var field of fieldsToSet) {
					if (field in this.style)
						return field;
				}
			}
			
			for (var field of fieldsToSet) {
				if (!field.fullmatch(/lang|training/))
					return field;
			}
			
			return fieldsToSet[0];
		},
		
		regexp_replace_operator_name(Field) {
			if (this.primary_key)
				return `operator[regexp_replace]${this.primary_key}[${Field}]`;
			return `operator[regexp_replace][${Field}]`;
		},
		
		change_setter(event){
			var setter = event.target.value;
			if (this.style[setter]) {
				this.functor = '';
			}
			else if (!this.functor){
				this.functor = 'regexp_replace';
			}
		},

		click_execute(event) {
			this.execute = !this.execute;
			event.preventDefault();
		},
		
		click_repeat(event) {
			this.repeat = !this.repeat;
			event.preventDefault();
		},
		
		input_operator(event){
			var {name, value} = event.target;
			name = name.split(/[\[\]]+/);
			name = name.slice(1, -1);
			setitem(this.operator, ...name, value);
		},
		
		keydown(event) {
			switch (event.key) {
			case 'ArrowRight':
				var input = event.target;
				var {length} = input.value;
				if (input.selectionStart == length && input.selectionEnd == length) {
					var {name} = input;
					if (name != 'new'){
						break;
					}
					
					var functor = input.previousElementSibling.previousElementSibling.previousElementSibling.value;
					if (functor != 'regexp_replace')
						break;
					
					var setter = input.previousElementSibling.previousElementSibling.value;
					
					if (!this.operator.regexp_replace) {
						this.operator.regexp_replace = {};
					}
					
					if (!this.operator.regexp_replace[setter])
						this.operator.regexp_replace[setter] = 'c';
					
					this.$nextTick(() => {
						input.nextElementSibling.focus();
					});
				}
				break;
			}
		},
		
		click_labelling(event) {
			var {table, fieldForLabelling:setter, autoLabellingType} = this;
			autoLabellingType = autoLabellingType[setter];
			switch (autoLabellingType) {
			case 'syntax':
				var url = `index.php?vue=${autoLabellingType}Labelling&table=${table}&setter=${setter}&repetition=6`;
				break;
			case 'entity':
				var url = `index.php?vue=${autoLabellingType}Labelling&table=${table}&setter=${setter}&textField=text`;
				break;
			}
			
			if (this.execute)
				url += "&execute=true";
			
			window.open(url, "_self", "toolbar=yes");
		},
		
		input_select(event) {
			var {target} = event;
			var $new = target.value;
			var {kwargs} = this;
			
			if (target.name.startsWith('set')) {
				var {set} = kwargs;
				if (set.isArray) {
					
				}
				else {
					var {eq} = set;
					if (target.name.match(/set\[eq\]\[1\]/)) {
						var [label, old] = eq;
						if (old != $new) {
							eq[1] = $new;
						}
					}
					else {
						var [old, dict] = eq;
						if (old != $new) {
							eq[0] = $new;
							if (dict.isString) {
								if (this.dtype[$new].fullmatch(/json|string/)) {
									eq[1] = {regexp_replace: [$new, '', '']};
								}
							}
							else {
								var [[fn, args]] = Object.entries(dict);
								for (var [i, arg] of enumerate(args)) {
									if (arg == old)
										args[i] = $new;
								}
							}
						}
					}
				}
			}
			else {
				var {order} = kwargs;
				if (target.name.match(/order\[0\]/)) {
					order[0] = $new;
				}
			}
		},
	},
	
	mounted() {
	},
}
</script>