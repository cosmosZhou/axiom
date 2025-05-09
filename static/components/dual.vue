<template>
	<div tabindex=2 @keydown=keydown_page>
		<mysql :host=host :user=user :token=token :sql=sql :kwargs=kwargs :rowcount=data.length :sample=sample ref=mysql></mysql>
		<template v-for="(data, index) of dataSampled">
			<table border=1 class=dictionary :index=index>
				<template v-for="{Field, value} of detailed_values(data)" :class=Field>
					<template v-if="value && value.isArray">
						<template v-if=value.length>
							<tr>
								<td :rowspan=value.length>{{Field}}</td>
								<td>
									<mysqlObject :name="`${Field}[${index}][0]`" :value=value[0]></mysqlObject>
								</td>
							</tr>
							<tr v-for="i of value.length - 1">
								<td>
									<mysqlObject :name="`${Field}[${index}][${i}]`" :value=value[i]></mysqlObject>
								</td>
							</tr>
						</template>
					    <tr v-else>
							<td>{{Field}}</td>
							<td></td>
						</tr>
					</template>
					<tr v-else>
						<td>{{Field}}</td>
						<td>
							<select v-if=dtype[Field].isArray :name="`${Field}[]`" :value=value>
								<option v-for="value of dtype[Field]" :value=value>{{value}}</option>
							</select>
							<span v-else-if=is_primary_key[Field]>
								<a :href=primary_key_url(value) :target=PRI>{{value}}</a>
								<input type=hidden :name="`${Field}[]`" :value=value />
							</span>
							<mysqlObject v-else :name="`${Field}[]`" :value=value></mysqlObject>
						</td>
					</tr>
				</template>
			</table>
		</template>
	</div>
</template>

<script>
console.log('import dual.vue');

import mysql from "./mysql.vue"
import mysqlObject from "./mysqlObject.vue"
import {props} from "../js/mysql.js"

export default {
    components: {mysql, mysqlObject},

	props: [...props, 'sample'],

    data() {
        return {
        	mounted: {},

        	_column_size: {},

        	desc: [],

        	dtype: {},
        };
    },

    computed: {
    	dataSampled() {
    		var {data} = this;
        	if (this.sample) {
        		return sample(data, this.sample < 1? parseInt(data.length * this.sample): this.sample);
        	}
        	else {
        		return data;
        	}
    	},

    	is_primary_key() {
			var dict = {};
			var {is_primary_key} = this.mysql;
			if (is_primary_key) {
				var {select} = this.kwargs;
				if (select) {
					if (select.isArray) {
						for (var key of select) {
							if (is_primary_key[key])
								dict[key] = true;
						}
					}
					else {
						if (is_primary_key[select])
							dict[select] = true;
					}
				}
			}
			return dict;
    	},

		primary_key_url() {
			return this.mysql.primary_key_url;
    	},

    	database() {
    		return this.mysql.database;
    	},

    	table() {
    		return this.mysql.table;
    	},

    	PRI() {
    		return this.mysql.PRI;
    	},

    	mysql() {
    		return this.mounted.mysql? this.$refs.mysql: {};
    	},
    },

    created() {
    	this.initialize_header();
    },

    methods: {
    	detailed_values(value) {
    		var values = [];
    		for (var {Field, Type} of this.desc) {
    			values.push({Field, Type, value: value[Field]});
    		}
    		return values;
    	},

    	stringify(value) {
    		if (!value)
    			return '';

    		if (value.isString)
    			return value.replace(/\n/g, '\\n');

    		if (value.isNumber)
    			return value;
    		return JSON.stringify(value);
    	},

    	initialize_header() {
    		this.dtype = {};
        	var {desc, dtype} = this;
        	desc.clear();
        	var {data} = this;
        	for (var obj of data) {
        		for (var Field in obj) {
        			if (dtype[Field]) {
						if (dtype[Field] == 'json') {
							var type = this.getType(obj[Field]);
							if (type == 'string') {
								try {
									obj[Field] = JSON.parse(obj[Field]);
									type = 'json';
								}
								catch (e) {
									console.log("Inconsistent type for", Field, "expected", dtype[Field], "got", type, "value", obj[Field]);
								}
							}
							else {
								console.log("Inconsistent type for", Field, "expected", dtype[Field], "got", type, "value", obj[Field]);
							}
						}
					}
					else {
						var type = this.getType(obj[Field]);
						if (type == 'string') {
							try {
								obj[Field] = JSON.parse(obj[Field]);
								type = 'json';
							}
							catch (e) {
							}
						}
        				dtype[Field] = type;
        				desc.push({Field, Type: dtype[Field]});
        			}
        		}
        	}
    	},

    	getType(value) {
    		if (value == null)
    			return 'json';

    		if (value.isString)
    			return 'string';

    		if (value.isNumber)
    			return 'number';

    		return 'json';
    	},

    	column_size(name){
    		var column_size = this._column_size[name];
    		if (column_size == null) {
    			column_size = Math.max(...this.data.map(tr => {
    				if (tr[name] && tr[name].isString)
    					return strlen(tr[name]);
    				return 10;
    			}));

    			this._column_size[name] = column_size;
    		}

    		return column_size;
    	},

    	coordinate(self){
    		var td = self.parentElement;
    		if (td.tagName == 'TD'){
    			var tr = td.parentElement;
    			var col = tr.children.indexOf(td);
    			var table = tr.parentElement;
    			var row = table.children.indexOf(tr);
    			return [row, col];
    		}
    		return [-1, -1];
    	},

    	focus(row, col, offset){
    		var table = this.$refs.table;
    		var tr = table.children[row];
    		var td = tr.children[col];
    		var input = td.firstElementChild;
    		input.focus();
    		if (input.tagName == 'INPUT'){
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
			case 'ArrowUp':
				event.preventDefault();
				var self = event.target;
				var [row, col] = this.coordinate(self);
				if (row > 0){
					--row;
					this.focus(row, col, self.selectionStart);
				}

				break;
			case 'ArrowDown':
				event.preventDefault();
				var self = event.target;
				var [row, col] = this.coordinate(self);
				if (row + 1 < this.$refs.table.children.length){
					++row;
					this.focus(row, col, self.selectionStart);
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

        blur(event, index){
        	var self = event.target;
        	var name = self.name.slice(0, -2);
        	if (self.value != this.data[index][name]){
        		this.data[index][name] = self.value;
        	}
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

table.dictionary {
	margin-bottom: 1em;
}

select {
	color: blue;
}

th {
	color: green;
}

</style>
