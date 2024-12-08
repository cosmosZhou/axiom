<template>
	<div @contextmenu.prevent=contextmenu tabindex=1 :class=class_report>
		<a :href=href_a :title="`id = ${id}, len(python) = ${python.length}`" :target=source>result from</a>&nbsp;
		<select v-model=source>
			<option v-for="source of ['mysql', 'torch', 'python', 'json']" :value=source>{{source}}</option>
		</select>
		&nbsp;
		<button type=button class=transparent @click=click_download ref=download><u>download</u></button> 
		<select v-model=ext>
			<option v-for="ext of ['txt', 'json']" :value=ext>{{ext}}</option>
		</select> file&nbsp;

		<latex2pythonContextmenu v-if=showContextmenu :left=left :top=top></latex2pythonContextmenu>
		<div class=float>
			<template v-if="correct == null"></template>
			<font v-else-if=correct color=green>√</font>
			<table v-else class=report border=1>
				<tr>
					<th>\</th><th>precision</th><th>recall</th>
				</tr>
				<tr>
					<td align=middle :class=class_training>reward</td>
					<fraction :numerator=true_positive :denominator=sum_predicted :operator="'='"></fraction>
					<fraction :numerator=true_positive :denominator=sum_labelling :operator="'='"></fraction>
				</tr>
			</table>
		</div>
		
	</div>
</template>

<script>
console.log('import latex2pythonTitle.vue');
import latex2pythonContextmenu from "./latex2pythonContextmenu.vue";
import fraction from "./fraction.vue"

export default {
	components : {latex2pythonContextmenu, fraction},
	
	props : [],
	
	data(){
		return {
			showContextmenu: false,
			left: 0,
			top: 0,
			source: 'mysql',
			ext: 'json',
			timestamp: null,
		};
	},
	
	computed: {
		class_report() {
			return '';
		},
		
		that() {
			return this.$parent.that;
		},
		
		correct() {
			return this.$parent.correct;
		},
		
		true_positive() {
			return this.$parent.true_positive;
		},
		
		sum_predicted() {
			return this.$parent.sum_predicted;
		},
		
		sum_labelling() {
			return this.$parent.sum_labelling;
		},
		
		class_training() {
			var {mysql_training} = this;
			return `training-${mysql_training}`;
		},
		
		training() {
			return this.$parent.training;
		},
		
		id() {
			return this.$parent.id;	
		},
		
		lang() {
			return this.$parent.lang;	
		},

		href_a(){
			var {href} = this.$parent.$parent.mysql;
			if (!href)
				return;
			
			var kwargs = {};
			if (this.$parent.normalize)
				kwargs.normalize = true;

			return href(this.id, this.source, kwargs);
		},
		
		table() {
			return this.$parent.table;
		},
		
		database() {
			return this.$parent.database;
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
		
		python: {
			get() {
				return this.$parent.python;	
			},
			
			set(text) {
				this.$parent.python = python;
			},
		},
		
		latex() {
			return this.$parent.latex;	
		},
		
		mysql_training() {
			return this.$parent.mysql_training;
		},
		
		command() {
			return this.$parent.command;
		},
		
		mysql() {
			return this.$parent.mysql;
		},
		
		is_torch(){
			return this.$parent.is_torch;
		},
	},
	
	created(){
		var kwargs = getParameter('kwargs');
		if (kwargs) {
			if (kwargs.python)
				this.source = 'python';
		}
		
		//this.initialize_timestamp();
	},
	
	methods: {
		async initialize_timestamp() {
			var res = await query(this.host, this.user, this.token, `select count, timestamp from log.rlhf where id = '${this.id}'`);
			if (res.length) {
				[[this.count, this.timestamp]] = res;
				//console.log(this.timestamp);
			}
		},

		change_checkbox(event) {
			this.$parent.$nextTick(()=>{
				this.$parent.async_render();
			});
			
			event.preventDefault();
		},
		
		click_download(event) {
			var self = this.$parent;
			var {id, training} = self;
			
			switch (this.ext){
			case 'json':
				var data = self.json;
				var filename = training < 0? 'predicted': 'corrected';
				filename = `${filename}-${id}`;
	    		break;
			case 'txt':
				if (training < 0)
					training = ~training;
				
				var data = {id, text: self.text, query: self.query, reply: self.reply, training};
				var filename = id;
				break;
			}
			
			saveFile(`${filename}.${this.ext}`, data)			
		},	
		
		contextmenu(event) {
			console.log("contextmenu: function(event)");
			self = event.target;				
			
			this.left = event.x + self.getScrollLeft();
			this.top = event.y + self.getScrollTop();
			
			this.showContextmenu = true;
			
			setTimeout(()=>{
				// Code that will run only after the entire view has been rendered					
				console.log('self = ', self);
				var contextmenu = self.parentElement.querySelector('.contextmenu');
				console.log('contextmenu = ', contextmenu);
				contextmenu.focus();					
			}, 100);
		},
	}
}
</script>

<style scoped>
a {
	color: purple;
}

div.float {
	float: right;
	z-index: 10000;
	opacity: 1;
}

div.report {
	height: 80px;
}

td.training-1 {
	color: red;
}

</style>