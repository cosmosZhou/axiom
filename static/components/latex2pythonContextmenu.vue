<template>
	<ul v-focus class=contextmenu :style="'left:%spx; top:%spx'.format(left, top)" tabIndex=2 @blur=blur @keydown=keydown>
		<li v-for="_, j of color.length" @click=click :style="style_font(j)" @mouseover=mouseover>
			<font :color=color[j]>{{hint[j]}}</font>
		</li>
	</ul>
</template>

<script>
import {keydown, directives} from "../js/contextmenu.js"
console.log('import latex2pythonContextmenu.vue');

export default {
	props : [ 'left', 'top'],

	data() {
		return {
			focusedIndex: -1,
			hint : ['property', 'delete', 'toggle training', 'rename', 'toggle server'],
			color : ['green',   'red',    'cyan',            'blue',   'orange',      ],
		};
	},

	created() {
	},
	
	computed: {
		length() {
			return this.color.length;
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
		
		table() {
			return this.$parent.table;	
		},
		
		text: {
			get() {
				return this.$parent.text;	
			},

			set(text) {
				this.$parent.text = text;
			},
		},
		
		reply() {
			return this.$parent.reply;
		},
		
		training() {
			return this.$parent.training;
		},
		
		lang() {
			return this.$parent.lang;
		},
		
		id() {
			return this.$parent.id;
		},
		
		mysql() {
			return this.$parent.mysql;
		},
	},
	
	methods : {
		coordinates() {
			var self = this.$parent;
			var table = self.$refs.table;
			return [this.left - table.getScrollLeft(), this.top - table.getScrollTop()];
		},
		
		style_font(j){
			if (this.focusedIndex == j)
				return `background: #ccc;`
		},
		
		blur(event){
			this.$parent.showContextmenu = '';
		},
		
		keydown(event){
			return keydown(this, event);
		},
		
		toggle_training() {
			this.mysql.toggle_training(this.$parent.$parent);
		},
		
		toggle_server() {
			return this.mysql.toggle_server();
		},

		delete() {
			this.mysql.delete_instance(this.$parent);
		},
		
		async rename() {
			var self = this.$parent;
			self.title.rename = true;
		},
		
		click(event){
			var self = event.target;
			this.$parent.showContextmenu = '';
			eval(`this.${self.textContent.replace(/ /g, '_')}`)();
		},		
		
        mouseover(event){                            
            var li = event.target;  
            var focusedIndex = this.$el.children.indexOf(li);
            if (focusedIndex != this.focusedIndex && focusedIndex >= 0){
            	this.focusedIndex = focusedIndex;
            }
        },        
	},
	
	directives,		
}
</script>

<style>
.contextmenu {
	margin: 0;
	background: #fff;
	z-index: 3000;
	position: absolute;
	list-style-type: none;
	padding: 5px 0;
	border-radius: 4px;
	font-size: 12px;
	font-weight: 400;
	color: #333;
	box-shadow: 2px 2px 3px 0 rgba(0, 0, 0, 0.3);
}

.contextmenu li {
	margin: 0;
	padding: 7px 16px;
	cursor: pointer;
}

</style>