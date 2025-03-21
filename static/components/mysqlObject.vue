<template>
	<template v-if="value == null"></template>
	<table v-else-if="value.constructor == Object" border=1 class=object>
		<template v-if=rows>
			<tr>
				<th v-for="field of keys">{{field}}</th>
			</tr>
			<template v-if=dict_key.length>
				<tr>
					<td v-for="key of dict_key" :rowspan=rows>
						<mysqlObject :name=node_name(key) :value=value[key]></mysqlObject>
					</td>
					<td v-for="key of list_key">
						<mysqlObject :name="node_name(key, 0)" :value=value[key][0]></mysqlObject>
					</td>
				</tr>
				<tr v-for="i of rows - 1">
					<td v-for="key of list_key">
						<mysqlObject :name="node_name(key, i)" :value=value[key][i]></mysqlObject>
					</td>
				</tr>
			</template>
			<tr v-else v-for="_, i of rows">
				<td v-for="key of list_key">
					<mysqlObject :name="node_name(key, i)" :value=value[key][i]></mysqlObject>
				</td>
			</tr>
		</template>
		<template v-else v-for="[key, value] of values">
			<template v-if="value && value.isArray">
				<template v-if=value.length>
					<tr>
						<td :rowspan=value.length>{{key}}</td>
						<td>
							<mysqlObject :name="node_name(key, 0)" :value=value[0]></mysqlObject>
						</td>
					</tr>
					<tr v-for="i of value.length - 1">
						<td>
							<mysqlObject :name="node_name(key, i)" :value=value[i]></mysqlObject>
						</td>
					</tr>
				</template>
				<tr v-else>
					<td>{{key}}</td>
					<td></td>
				</tr>
			</template>
			<tr v-else>
				<td>{{key}}</td>
				<td>
					<mysqlObject :name=node_name(key) :value=value></mysqlObject>
				</td>
			</tr>
		</template>
	</table>
	<textarea v-else-if=value.isString :name=name :value=value :rows=value.rows() :cols=value.cols() @change=change @keydown="keydown_textarea"></textarea>
	<table v-else-if=value.isArray border=1 class=object>
		<tr v-for="value, i of value">
			<td v-if="value == null"></td>
			<td v-else-if=value.isArray v-for="value, j of value">
				<mysqlObject :name="node_name(null, [i, j])" :value=value></mysqlObject>
			</td>
			<td v-else>
				<mysqlObject :name="node_name(null, i)" :value=value></mysqlObject>
			</td>
		</tr>
	</table>
	<input v-else :name=name :value=value @change=change />
</template>

<script>
import {head_line_offset, last_line_offset} from "../js/textarea.js"
console.log('import mysqlObject.vue');

export default {
    components: {},

	props: ['value', 'name', 'order'],
	
    data() {
        return {
        	mounted: {},
        };
    },
    
    computed: {
    	keys() {
    		return [...this.dict_key, ...this.list_key];
    	},
    	
		values() {
			var values = Object.entries(this.value);
			switch (this.order) {
			case 'asc':
				values.sort((a, b) => a[0].localeCompare(b[0]));
				break;
			case 'desc':
				values.sort((a, b) => b[0].localeCompare(a[0]));
				break;
			}
			return values;
		},

    	rows() {
    		return this.list_dict_split.rows;
    	},

    	dict_key() {
    		return this.list_dict_split.dict_key;
    	},
    	
    	list_key() {
    		return this.list_dict_split.list_key;
    	},
    	
    	list_dict_split() {
    		var {value} = this;
    		var dict_key = [];
    		var list_key = [];
    		for (var [key, item] of Object.entries(value))	{
    			var item = value[key];
    			if (item && item.isArray && item.length > 1) {
    				list_key.push(key);
    			}
    			else {
    				dict_key.push(key);
    			}
    		}
			
    		if (list_key.length > 1 && is_same(list_key.map(key => value[key].length)))
    			return {rows: value[list_key[0]].length, dict_key, list_key};

    		return {};
    	},

    	database() {
    		return this.mysql.database;
    	},
    	
    	PRI() {
    		return this.mysql.PRI;
    	},
    	
    	mysql() {
    		return this.mounted.mysql? this.$refs.mysql: {};
    	},
    	
    	desc() {
    		var desc = this.mysql.desc;
    		if (desc)
    			return desc;
    		return [];
    	},
    	
    	api() {
    		var api = this.mysql.api;
    		if (api)
    			return api;
    		return {};
    	},
    	
    	api_parameters() {
    		var api = this.api;
    		for (var Field in api) {
    			var {url : api_url, inputs: api_inputs} = api[Field];
    			return {api_inputs, api_url, api_output: Field};
    		}

    		return {};
    	},
    	
    	api_url() {
    		return this.api_parameters.api_url;
    	},
    	
    	api_inputs() {
    		return this.api_parameters.api_inputs;
    	},
    	
    	api_output() {
    		return this.api_parameters.api_output;
    	},
    	
    	dtype() {
    		var dtype = this.mysql.dtype;
    		if (dtype)
    			return dtype;
    		return {};
    	},
    	
		is_torch() {
			return getParameterByName('torch') || this.kwargs.kwargs && this.kwargs.kwargs.torch;
		},
		
		is_mysql() {
			return getParameterByName('mysql') || getParameterByName('cmd') == 'select' || this.cmd == 'update';
		},

		compare() {
			if (this.is_torch)
				return 'torch';
		},
    },
    
    created() {
    },
    
    methods: {
		node_name(name, i) {
			if (name) {
				var values = Object.values(this.value);
				if (this.name) {
					if (i == null)
						return `${this.name}[${name}]`;
						
					if (i == 0 && values.length == 1 && (!values[0] || !values[0].isArray)) {
						return `${this.name}[${name}]`;
					}
					
					return `${this.name}[${name}][${i}]`;
				}

				if (i == null)
					return name;
				
				if (i == 0 && values.length == 1 && (!values[0] || !values[0].isArray)) {
					return name;
				}
				
				return `${name}[${i}]`;
			}
			else {
				if (i.isArray) {
					var [i, j] = i;
					return `${this.name}[${i}][${j}]`;
				}
				else
					return `${this.name}[${i}]`;
			}
		},
    	
    	get_string(value) {
    		return value.toString().replace('\n', '\\n');
    	},
    	
    	get_size(value) {
    		return this.get_string(value).strlen();
    	},

    	coordinate(self){
    		var td = self.parentElement;
    		if (td.tagName == 'TD'){
    			var tr = td.parentElement;
    			var col = tr.children.indexOf(td);
    			var table = tr.parentElement;
    			var row = table.children.indexOf(tr);
    			return [row, col, table.children.length];
    		}
    		return [-1, -1];
    	},
    	
    	focus(row, col, offset, table){
    		table ||= this.$refs.table;
    		var tr = table.children[row];
    		var td = tr.children[col];
    		var input = td.firstElementChild;
    		input.focus();
    		if (input.tagName == 'INPUT' || input.tagName == 'TEXTAREA'){
    			if (offset < 0){
    				offset.value.length;
    			}
    			
    			input.selectionStart = offset;
    			input.selectionEnd = offset;
    		}
    	},
    	
    	keydown_table(event){
			var self = event.target;
			var key = event.key;
			switch (key){
			case 'S':
			case 's':
				if (!event.ctrlKey)
					break;
				event.preventDefault();
				
				this.$nextTick(()=>{
					form.submit();
				});
			
				break;
				
			case 'Z':
			case 'z':
				if (!event.ctrlKey)
					break;
				
				this.undoer.undo();
				break;
				
			case 'ArrowUp':
				if (self.tagName == 'TEXTAREA') {
					var selectionStart = head_line_offset(self);
					if (selectionStart == null) {
						break;
					}
					var table = self.parentElement.parentElement.parentElement;
				}
				else {
					var {selectionStart} = self;
					var table = null;
				}
				
				event.preventDefault();
				var self = event.target;
				var [row, col] = this.coordinate(self);
				if (row > 0){
					--row;
					this.focus(row, col, selectionStart, table);
				}
				
				break;
			case 'ArrowDown':
				var self = event.target;
				if (self.tagName == 'TEXTAREA') {
					var selectionStart = last_line_offset(self);
					if (!selectionStart) {
						break;
					}
					var table = self.parentElement.parentElement.parentElement;
				}
				else {
					var {selectionStart} = self;
					var table = null;
				}
				
				event.preventDefault();
				var [row, col, rows] = this.coordinate(self);
				if (row + 1 < rows){
					++row;
					this.focus(row, col, selectionStart, table);
				}
				
				break;
			case 'ArrowLeft':
				
				var self = event.target;
				if (self.tagName == 'SELECT' || !self.selectionStart){
					event.preventDefault();
					var [row, col] = this.coordinate(self);
					if (col > 0){
						--col;
					}
					else{
						--row;
						col = self.parentElement.parentElement.children.length - 2;
					}
					this.focus(row, col, -1);
				}
				
				break;
			case 'ArrowRight':
				
				var self = event.target;
				if (self.tagName == 'SELECT' || self.selectionStart == self.value.length){
					event.preventDefault();
					var [row, col] = this.coordinate(self);
					if (col + 1 < self.parentElement.parentElement.children.length - 1){
						++col;
					}
					else{
						row++;
						col = 0;
					}
					this.focus(row, col, 0);
				}
				
				break;
			}
    	},

    	keydown_textarea(event){
			var self = event.target;
			var key = event.key;
			switch (key){
			case 'Enter':
				if (!event.ctrlKey)
					break;
				
				var input = event.target;
				var value = input.value;
				var {selectionStart} = input;
				
				var former = value.slice(0, selectionStart).trim();
				var latter = value.slice(selectionStart).trim();

				var {name} = input;
				var m = name.match(/^(\w+)\[(\d+)\]/);
				if (m) {
					var attr = m[1];
					var index = parseInt(m[2]);
					var indices = name.slice(m[0].length);
					var paths = [];
					for (var m of indices.matchAll(/\[(\d+)\]|\[([^\[\]]+)\]/g)) {
						paths.push(m[2] || parseInt(m[1]));
					}

					var self = this;
					for (var _ of range(paths.length)) {
						self = self.$parent;
					}

					var i = paths.pop();
					console.assert(i.isInteger, "i.isInteger");
					var array = getitem(self.data[index][attr], ...paths);
					array[i] = former;
					array.insert(i + 1, latter);
					this.set_training();
				}
				break;
			}
		},
		
        async process(name, data) {
    		var [name, ext] = split_filename(name);
    		var array = [];
    		switch (ext) {
    		case 'json':
    			if (data.isString)
                	array = JSON.parse(data);
    			else
    				array = data;
                if (!Array.isArray(array)){
                	array = [array];
                }
                break;

    		case 'txt':
    		case 'csv':
            	for (var line of data.split('\n')){
            		var obj = {};
            		for (var [{Field, Type}, value] of zip(this.desc, line.split('\t'))) {
            			obj[Field] = value;
            		}
            		array.push(obj);
            	}
            	break;
                
			case 'xlsx':
				var workbook = XLSX.read(data, {type: 'array'});
		        for (var sheet in workbook.Sheets) {
		            if (workbook.Sheets.hasOwnProperty(sheet)) {
		                for (var data of XLSX.utils.sheet_to_json(workbook.Sheets[sheet])) {
		                	for (var key in this.dtype) {
		                		if (data[key] == null) {
		                			var dtype = this.dtype[key];
		                			switch (dtype) {
		                			case 'float':
		                				data[key] = 0;
		                				break;
		                			case 'string':
		                				data[key] = '';
		                				break;
		                			case 'int':
		                				if (key == this.PRI) {

		                				}
		                				else if (key == 'training') {
		                					data[key] = ~1;
		                				}
		                				else {
		                					data[key] = 0;
		                				}
		                				break;
		                			default:
		                				if (dtype.isArray) {
		                					data[key] = dtype[0];
		                				}
		                				else {
		                					data[key] = '';
		                				}
		                				break;
		                			}
		                		}
		                	}
		                	array.push(data);
		                }
		            }
		        }
				break;
            }

    		this.insert(array);
        },
        
    	async insert(data) {
        	var database = this.database;
        	var table = this.table;
			var training = getParameterByName("training");
			if (training)
				training = ~training;
			else
				training = ~0;

			for (var obj of data) {
				if (obj.training == null)
					obj.training = training;
				else if (obj.training >= 0) {
					obj.training = ~obj.training;
				}
			}
			
			var {PRI} = this;
			if (this.dtype[PRI] == 'int') {
	        	var [ret] = await query(this.host, this.token, `select max(${PRI}) as id from ${database}.${table}`);
	        	var primary_key = ret[PRI];
	        	var primary_key = primary_key == null? 0: parseInt(primary_key);
	        	for (var obj of this.data) {
	        		if (obj[PRI] > primary_key)
	        			primary_key = obj[PRI];
	        	}

				for (var obj of data) {
					if (!obj[PRI])
						obj[PRI] = ++primary_key;
				}
			}

			this.data.push(...data);
    	},

        change(event){
			var {name} = this;
			var m = name.match(/^(\w+)\[(\d+)\]/);
			if (m) {
				var attr = m[1];
				var index = parseInt(m[2]);
				var indices = name.slice(m[0].length);
				var paths = [];
				for (var m of indices.matchAll(/\[(\d+)\]|\[([^\[\]]+)\]/g)) {
					paths.push(m[2] || parseInt(m[1]));
				}

				var self = this;
				for (var _ of range(paths.length)) {
					self = self.$parent;
				}
				
				if (self[attr] === undefined)
					self = self.data[index];
				setitem(self[attr], ...paths, event.target.value);
			}
    		this.set_training();
        },
        
        set_training() {
        	this.$parent.set_training(this);
        },
    },
    
    mounted() {
    },
    
    unmounted() {
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

<style scoped>
table {
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;
	background: transparent;
}

th.training, tr.training, td.training {
	display: none;
}

input {
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;
	background: transparent;
	border: none;
	border-style: none;
	padding: 0px 0px 0px 0px;
}

input:focus {
	outline: none;
	caret-color: rgb(127, 0, 85);
}

input.float, input.int {
	color: red;
}

select {
	color: blue;
}

textarea {
	resize: none;
	overflow: hidden;
	border: none;
	height: auto;
	font-family: Consolas;
}

textarea:focus {
	color: red;
	outline: none;
	caret-color: rgb(127, 0, 85);
}

div.float {
	float: right;
	z-index: 10000;
	opacity: 1;
}

td.false {
	color: red;
}

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

button.transparent:hover{
	background-color: red;
}

</style>
