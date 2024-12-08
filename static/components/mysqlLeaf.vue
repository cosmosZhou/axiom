<template>
	<span>
		<select v-if="option && !insert" :name=name :value=value :style="style_select(value, color)" @input=input_select @keydown=keydown_select>
			<option value=''>___</option>
			<template v-for="option of option">
				<option v-if=option.isString :value=option>{{option}}</option>
				<optgroup v-else v-for="(option, label) of option" :label=label>
					<option v-for="option of option" :value=option>{{option}}</option>
				</optgroup>
			</template>
		</select>
		<input v-else type=text :name=name :value=value :size=input_size @input=input_kwargs @keydown=keydown_input />
		<template v-if=!noSpace>{{' '}}</template>
	</span>
</template>

<script>
console.log('import mysqlLeaf.vue');

export default {
	components: {},
	
	props : ['name', 'value', 'option', 'color', 'noSpace'],
	
	data(){
		return {
			insert: null,
		};
	},

	created(){
		//var {value, name, option} = this;
		//console.log({value, name, option});
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
			var {value, option} = this.$props;
			if (option) {
				if (value) {
					if (!option.contains(value)) {
						return [value, ...option];
					}
				}
				return option;
			}
		},
		
		input_size() {
			var {value} = this;
			if (value) {
				value = value.toString();
				return Math.max(value.strlen(), 4);
			}
			return 4;
		},
		
		style_select() {
			return this.$parent.style_select;
		},
		
		kwargs() {
			return this.$parent.kwargs;
		},
		
		PRI() {
			return this.$parent.PRI;
		},
		
		input_kwargs() {
			return this.$parent.input_kwargs;
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
		
		numeric_functions() {
			return this.$parent.numeric_functions;
		},
		
		jsonobj_functions() {
			return this.$parent.jsonobj_functions;
		},

		textual_functions() {
			return this.$parent.textual_functions;
		},
	},
	
	methods: {
		input_select(event) {
			var {target} = event
			var {_value, value} = target;
			if (_value == value)
				return;
			
			var {name, parentElement} = target;
			if (this.is_textual_function) {
				if (this.is_textual_function(value) || this.is_jsonobj_function(value)) {
					name += `[${value}]`;
					
					if (this.is_aggregate_function(value)) {
						var {value} = this.$parent;
						if (value.select) {
							if (!value.group) {
								value.group = this.PRI;
								value.having = {eq: [{count: [this.PRI]}, '']};
							}
						}
						value = this.PRI;
					}
					else {
						switch (value) {
						case 'json_object':
							if (this.value.isString) {
								if (this.value == '*') {
									value = [this.PRI, this.PRI];
								}
								else {
									value = [this.value, this.value];
								}
							}
							else if (this.value.isArray) {
								value = [this.PRI, this.value];
							}
							else {
								value = [Object.keys(this.value)[0], this.value];
							}
	
							break;
	
						case 'regexp_replace':
							if (this.value.isString) {
								if (this.value == '*') {
									value = [this.PRI, '', ''];
								}
								else {
									value = [this.value, '', ''];
								}
							}
							else if (this.value.isArray) {
								value = [this.PRI, '', ''];
							}
							else {
								value = [Object.keys(this.value)[0], '', ''];
							}
	
							break;
							
						case 'regexp_substr':
						case 'substring':
						case 'left':
						case 'right':
							if (this.value.isString) {
								if (this.value == '*') {
									value = [this.PRI, ''];
								}
								else {
									value = [this.value, ''];
								}
							}
							else if (this.value.isArray) {
								value = [this.PRI, ''];
							}
							else {
								value = [Object.keys(this.value)[0], ''];
							}
							break;
							
						case '*':
							value = this.value;
							break;

						case 'json_extract':
							if (this.value.isString) {
								value = [this.value, "$."];
							}
							else if (this.value.isArray) {
								value = [this.value[0], "$."];
							}
							else {
								value = [this.value, "$."];
							}
	
							break;
							
						case 'json_valid':
							if (this.value.isArray) {
								value = [this.value[0]];
							}
							else {
								value = [this.value];
							}
	
							break;
							
						default:
							value = this.PRI;
							break;
						}
					}
	
					this.input_kwargs({target : {name, value}});
					
					this.$parent.$nextTick(()=>{
						mysql.querySelector(`select[name="${name}"]`).focus();
					});
				}
				else if (this.is_numeric_function(value)) {
					name += `[${value}]`;
					this.input_kwargs({target : {name, value : this.PRI}});
					
					this.$parent.$nextTick(()=>{
						parentElement.querySelector(`select[name="${name}"]`).focus();
					});
				}
				else {
					switch (value) {
					case 'distinct':
						name += `[${value}]`;
						this.input_kwargs({target : {name, value : this.PRI}});
						
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[name="${name}"]`).focus();
						});
						break;
					case 'if':
						name += `[${value}]`;
						this.input_kwargs({target : {name, value : [{eq: [this.PRI, 0]}, 1, 0]}});
						
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[class="${name}"]`).focus();
						});
						break;
						
					case 'tables':
						name += `[in]`;
						this.input_kwargs({target : {name, value : ['tables', 'corpus']}});
						
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[class="${name}"]`).focus();
						});
						break;
						
					case 'create':
						name += `[create]`;
						this.input_kwargs({target : {name, value : {table : {corpus: 'markush'}}}});
						
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[class="${name}"]`).focus();
						});
						break;

					case 'rand':
						this.input_kwargs({target : {name: name, value : 'rand()'}});
						parentElement = parentElement.parentElement;
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[name="${name}"]`).focus();
						});
						break;
						
					default:
						this.input_kwargs(event);
					}
				}
				if (this.$parent.input_select) {
					this.$parent.input_select(event);
				}
			}
			else {
				var parent = this.$parent.$parent;
				if (parent.input_select) {
					parent.input_select(event);
				}
			}
		},
		
		nextElementSibling(element) {
			var next = element.nextElementSibling;
			while (next) {
				if (next.name)
					return next;
				
				next = next.nextElementSibling;
			}
		},
		
		keydown_select(event) {
			var select = event.target;
			switch (event.key) {
			case "ArrowUp":
				if (!select.selectedIndex) {
					//select.selectedIndex = select.children.length - 1;
					select.value = select.children.back().value;
					this.func = select.value;
					event.preventDefault();
					break;
				}
				break;
			case "ArrowLeft":
				event.preventDefault();
				var m = select.name.fullmatch(/select\[(group_concat)\]\[(\d)\]/);
				if (m) {
					var func = m[1];
					var index = parseInt(m[2]);
					switch (func) {
					case 'group_concat':
						switch (index) {
						case 0:
							select.previousElementSibling.focus();
							break;
						case 1:
						case 2:
							select.previousElementSibling.previousElementSibling.focus();
							break;
						}
						break;
					}
					break;
				}
				
				var m = select.name.fullmatch(/(select)/);
				if (m) {
					select.previousElementSibling.focus();
					break;
				}
				
				break;
			case "ArrowRight":
				event.preventDefault();
				if (event.ctrlKey) {
					var regexp = [...this.numeric_functions, ...this.textual_functions, ...this.jsonobj_functions].join('|');
					regexp = new RegExp(`\\[(${regexp})\\](?:\\[(\\d)\\])?$`);
					var m = select.name.match(regexp);
					var {parentElement} = select;
					if (m) {
						var func = m[1];
						var index = m[2]?? 0;
						var index = parseInt(index);
						var func_args = this.$parent.value[func];
						if (!func_args.isArray) {
							func_args = [func_args];
							this.$parent.value[func] = func_args;
						}
						
						if (func_args[index + 1]) {
							this.nextElementSibling(select).focus();
						}
						else {
							if (func.match(/group_concat/)) {
								if (index == 0) {
									func_args[index] = [func_args[index], {order: this.PRI}];
									var name = select.name + '[0][1][order]';
									this.$parent.$nextTick(()=>{
										parentElement.querySelector(`select[name="${name}"]`).focus();
									});
								}
							}
							else {
								func_args[index + 1] = this.PRI;
								this.$parent.$nextTick(()=>{
									this.nextElementSibling(select).focus();
								});
							}
						}
						
						break;
					}
					
					var m = select.name.match(/select(?:\[(\d)\])?$/);
					if (m) {
						if (m[1]) {
							var index = parseInt(m[1]) + 1;
							var name = select.name.replace(/(?:\[(\d)\])?$/, `[${index}]`);
							this.$parent.value.select = [...this.$parent.value.select, deepCopy(this.$parent.value.select.back())];
						}
						else {
							var name = select.name + '[1]';
							this.$parent.value.select = [this.$parent.value.select, deepCopy(this.$parent.value.select)];
						}
							
						var {parentElement} = select;
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[name="${name}"]`).focus();
						});

						break;
					}
					
					var m = select.name.match(/(\[order\]|order)(\[0\])?$/);
					if (m) {
						if (this.$parent.value.order.isArray) {
							this.$parent.value.order = [...this.$parent.value.order, 'desc'];
						}
						else {
							this.$parent.value.order = [this.$parent.value.order, 'desc'];
						}
						break;
					}

					var m = select.name.match(/(\[from\]|from)$/);
					if (m) {
						if (this.$parent.$parent.initialize_where()) {
							console.log(this.$parent.$parent.value.where);
						}
						break;
					}

					var m = select.name.match(/^select\[as\]\[0\]$/);
					if (m) {
						var {value} = this.$parent.$parent
						var {select} = value;
						value.select = [select, deepCopy(select)];
						var name = 'select[1][as][0]';
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[name="${name}"]`).focus();
						});
						break;
					}
				}
				else if (event.shiftKey) {
					console.log(select);
				}
				else {
					var m = select.name.fullmatch(/select/);
					if (m) {
						select.nextElementSibling.focus();
						break;
					}
				}
				
				break;

			case "Insert":
				this.insert = true;
				var {parentElement, name} = select;
				this.$nextTick(()=>{
					var input = parentElement.querySelector(`input[name="${name}"]`);
					input.selectionStart = 0;
					input.selectionEnd = input.value.length;
					input.focus();
				});
				break;

			case "F2":
				var hit = false;
				if (this.$parent.value.select === this.value) {
					this.$parent.value.select = {as: [this.value, this.PRI]};
					hit = true;
				}
				else if (this.$parent.value.select) {
					var index = this.$parent.value.select.indexOf(this.value);
					if (index >= 0) {
						this.$parent.value.select[index] = {as: [this.value, this.PRI]};
						hit = true;
					}
				}

				if (hit) {
					var {parentElement, name} = target;
					name += '[as][1]';
					this.$parent.$nextTick(()=>{
						parentElement.querySelector(`select[name="${name}"]`).focus();
					});
				}
				break;
			case "Delete":
				this.$parent.delete(this.value);
				break;
			default:
				break;
			}
		},
		
		keydown_input(event) {
			var {target} = event;
			var {parentElement} = target;
			if (parentElement.tagName == 'SPAN')
				parentElement = parentElement.parentElement;
			switch (event.key) {
			case "F2":
				var hit = false;
				if (this.$parent.value.select === this.value) {
					this.$parent.value.select = {as: [this.value, this.PRI]};
					hit = true;
				}
				else if (this.$parent.value.select) {
					var index = this.$parent.value.select.indexOf(this.value);
					if (index >= 0) {
						this.$parent.value.select[index] = {as: [this.value, this.PRI]};
						hit = true;
					}
				}

				if (hit) {
					var {parentElement, name} = target;
					name += '[as][1]';
					this.$parent.$nextTick(()=>{
						parentElement.querySelector(`select[name="${name}"]`).focus();
					});
				}
				break;

			case "ArrowRight":
				if (event.ctrlKey) {
					event.preventDefault();
					var regexp = [...this.numeric_functions, ...this.textual_functions, ...this.jsonobj_functions].join('|');
					regexp = new RegExp(`\\[(${regexp})\\](?:\\[(\\d)\\])?$`);
					var m = target.name.match(regexp);
					if (m) {
						var func = m[1];
						var index = m[2]?? 0;
						var index = parseInt(index);
						var func_args = this.$parent.value[func];
						if (!func_args.isArray) {
							func_args = [func_args];
							this.$parent.value[func] = func_args;
						}
						
						if (func_args[index + 1]) {
							this.nextElementSibling(target).focus();
						}
						else {
							switch (func) {
							case 'group_concat':
								func_args[index] = [func_args[index], {order: this.PRI}];
								var name = target.name + '[0][1][order]';
								this.$parent.$nextTick(()=>{
									parentElement.querySelector(`select[name="${name}"]`).focus();
								});
								break;
							case 'regexp_replace':
								func_args.push(1, 0, 'c');
								var name = target.name.replace(new RegExp(`\\[${index}\\]$`), '[5]');
								this.$parent.$nextTick(()=>{
									parentElement.querySelector(`select[name="${name}"]`).focus();
								});
								break;
							default:
								func_args[index + 1] = this.PRI;
								this.$parent.$nextTick(()=>{
									this.nextElementSibling(target).focus();
								});
								break;
							}
						}
						
						break;
					}
					
					var m = target.name.match(/select(?:\[(\d)\])?$/);
					if (m) {
						if (m[1]) {
							var index = parseInt(m[1]) + 1;
							var name = target.name.replace(/(?:\[(\d)\])?$/, `[${index}]`);
							this.$parent.value.select = [...this.$parent.value.select, deepCopy(this.$parent.value.select.back())];
						}
						else {
							var name = target.name + '[1]';
							this.$parent.value.select = [this.$parent.value.select, deepCopy(this.$parent.value.select)];
						}
							
						var {parentElement} = target;
						this.$parent.$nextTick(()=>{
							parentElement.querySelector(`select[name="${name}"]`).focus();
						});

						break;
					}
					
					var m = target.name.match(/\[order\]$/);
					if (m) {
						this.$parent.value.order = [this.$parent.value.order, 'desc'];
						break;
					}
					
					var m = target.name.match(/(\[from\]|from)$/);
					if (m) {
						var {PRI} = this;
						PRI = 'pn';
						var columns = [[PRI, {varchar: 36}, {path: '$'}]];
						var json_table = [PRI, ['$[*]', {columns}]];
						var as = [{json_table}, '_t'];
						//console.log({json_table});
						this.$parent.$parent.value.inner_join = {as};
						break;
					}
				}
				
				break;
				
			default:
				break;
			}
		},
	},
}
</script>