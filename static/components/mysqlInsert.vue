<template>
	<span class=insert>
		<select class=cmd v-model=$parent.cmd>
			<option v-for="value of cmds" :value=value>{{value}}</option>
		</select>
		<font color=blue> into </font><mysqlDot :name="'into'" :value=value.into :noSpace=true></mysqlDot>({{args.join(", ")}}) 
		values(<template v-for="{Field, Type}, i of desc">
			<select v-if="Array.isArray(dtype[Field])" :name=Field :value=get_initial_value(Field) @input=input_kwargs>
				<option value=''>{{'_'.repeat(Math.max(...dtype[Field].map(el => el.length)))}}</option>
				<option v-for="value of dtype[Field]" :value=value>{{value}}</option>
			</select>
			<textarea v-else-if="Type == 'text' || Type == 'json'" v-focus :name=Field @change=change_input :value=get_initial_value(Field) @input=input_kwargs @keydown=keydown :placeholder=Field></textarea>
			<input v-else v-focus type=text :name=Field @change=change_input :value=get_initial_value(Field) :style=style_input(Field) @input=input_kwargs @keydown=keydown :size=input_size(Field) :placeholder=Field />
			<template v-if="i < desc.length - 1">, </template>
		</template>), (<div class=upload>
	         upload
	         <input ref=input type=file @change=change_file multiple=multiple>
	         <progress v-if=progress.max :value=progress.value :max=progress.max></progress>
	    </div>)
	    <div @drop.stop.prevent=drop @dragover.stop.prevent=dragover class=drop></div>
    </span>
</template>

<script>
console.log('import mysqlInsert.vue');
import mysqlDot from "./mysqlDot.vue"

export default {
	components: {mysqlDot},
	
	props : ['kwargs'],
	
	data(){
		var data = this.$parent.$data;
		data.files = {};
		data.progress = {value: null, max: null};
		// console.log(this.kwargs);
		var {kwargs} = this;
		var {where} = kwargs;
		if (where){
			var {and} = where;
			if (and){
				if (and.isArray) {
					for (var {eq, regexp} of and){
						var arr = eq || regexp;
						if (arr){
							var [Field, Value] = arr;
							if (kwargs[Field] == null)
								kwargs[Field] = Value;
						}
					}
				}
			}
		}
		return data;
	},

	async created(){
		var self = this;
		
		var {body} = document;

		body.addEventListener("drop", event => {
			event.stopPropagation();
			event.preventDefault();
			self.process_files(event.dataTransfer.files);
		});

		body.addEventListener("dragover", event => {
			event.stopPropagation();
			event.preventDefault();
		});
	},
	
	computed: {
		change_table(){
			return this.$parent.change_table;
		},
		
		change_database(){
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
		
		value() {
			return this.kwargs;
		},
		
		database() {
			return this.$parent.database;
		},
		
		table() {
			return this.$parent.table;
		},
		
		desc() {
			var desc = [...this.$parent.desc];
			var index = 0;
			for (var {Field} of desc){
				if (Field == 'training'){
					desc.delete(index);
					break;
				}
				index++;
			}
			
			return desc;
		},
		
		change_input(){
			return this.$parent.change_input;
		},

		style_select_table(){
			return this.$parent.style_select_table;
		},
		
		style_select() {
			return this.$parent.style_select;
		},
		
		style_input(){
			return this.$parent.style_input;
		},
		
		input_kwargs(){
			return this.$parent.input_kwargs;
		},
		
		args(){
			var args = [];
			for (var {Field} of this.desc){
				if (Field != 'training')
					args.push(Field);
			}
			return args;
		},
	},
	
	methods: {
		get_initial_value(Field) {
			var obj = getParameterByName(Field);
			if (obj && obj.constructor == Object)
				return JSON.stringify(obj);
			return obj || this.kwargs[Field];
		},
		
		input_size(Field) {
			var value = this.get_initial_value(Field);
			if (value) {
				value = value.toString();
				return Math.max(value.strlen(), 4);
			}
			return 4;
		},
		
		drop(event){
			this.process_files(event.dataTransfer.files);
		},
		
		dragover(event){
		},
		
		process(name, text){
			var self = this.$root.$refs[this.table.hump] || this.$root.$refs.mysqlTable;
			self.process(name, text);
			if (self.download_option)
				self.download_option.file = name;
		},
		
		process_files(files){
			//console.log(files);
			var self = this;
			var duplicates = [];
			
			var {progress} = self;
			for (let file of files){
				if (this.files[file.name]){
					duplicates.push(file.name);
					continue;
				}
				console.log('file.name = ' + file.name);
				
				this.files[file.name] = true;
				
				var reader = new FileReader();
				
				reader.onload = function(event) {
					self.process(file.name, this.result);
				};
				
	            progress.max = file.size;
	            progress.value = 0;
                reader.onprogress = event => {
                    progress.value = event.loaded;
                };

				switch (file.type){
				case "image/jpeg":
				case "image/png":
					reader.readAsDataURL(file);
					break;
					
				case "application/pdf":
				case "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet":
					reader.readAsArrayBuffer(file);
					break;

				default:
					reader.readAsText(file);
					break;
				}
			}
			
			if (duplicates.length)
				alert(`files already uploaded:\n${duplicates.join('\n')}`);
		},
		
		change_file(event){
			this.process_files(event.target.files);
		},
		
		keydown(event) {
			if (event.key == 'Enter'){
				if (event.target.tagName == 'TEXTAREA') {
					if (!event.ctrlKey)
						return;
				}

				event.preventDefault();
				var data = {};
				for (var name of this.args){
					data[name] = this.get_initial_value(name);
				}
				
				console.log("insert data", data);
				
				if (data.training == null) {
					var training = getParameterByName('training');
					training = training? parseInt(training): randrange(2);
					data.training = ~training;
				}
				else {
					var training = parseInt(data.training);
					if (training >= 0)
						data.training = ~training;
				}
				
				this.process('.json', data);
			}
		},
	},
	
	mounted(){
	},
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	var {instance} = binding;
		    	if (instance.$parent.focus == false)
		    		return;
		    	
	    		el.focus();
		    },
		},
	},
}
</script>

<style scoped>
input[type=file] {
	color: transparent;
	
	height: 130%;
	width: 6.4em;
	
	position: absolute;
	
	bottom:0;
	left:0;
	right: 0;
	top: 0;
	
	font-size: 100px;
	
	z-index:1;
	opacity:0;
	filter: alpha(opacity=0);
	-ms-filter: alpha(opacity=0);
}

.upload {
	position: relative;
	display: inline-block;
	overflow: hidden;
	
	width:100px;
	height:30px;
	line-height:30px;
	
	top: 10px;
	
	border:1px solid #ddd;
	background:#f6f6f6;
	text-align:center;
	
	color:#333;
	
	font-size: 25px;
}

div.drop {
	position: absolute;
	top: 0;
	bottom:0;
	left:0;
	right:0;
	overflow: hidden;
	overflow-y: auto;
	-webkit-overflow-crolling:touch;
	z-index: -1000;
}

textarea {
	resize: none;
	overflow: hidden;
	border: none;
}

textarea:focus {
	color: red;
	outline: none;
	caret-color: rgb(127, 0, 85);
}

</style>