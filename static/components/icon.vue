<template>
	<div v-show=visible @click=click @dblclick.prevent=dblclick @focus=focus @blur=blur @keydown=keydown @contextmenu.prevent=contextmenu>
		<br v-for="i of lines" /> 
		<font v-if="tagName == 'FONT'">{{text}}</font> 
		<input v-else-if="tagName == 'INPUT'" :size='text.length + 1' :value=text @blur=blur_input @change=change_input>
		<template v-else>{{text}}</template>
	</div>
</template>

<script>
console.log('import icon.vue');
var previousKey = '';
var previousTime = null;	
export default {
	props : [ 'text', 'lines'],
	
	data() {
		return {
			tagName: '',
			visible: true,
		};
	},
	
	methods : {
		dblclick(event) {
			this.$parent.dblclick(event);
		},			
		
		click(event) {
			this.focus(event);
		},
		
		focus(event) {
			this.tagName = 'FONT';
		},

		blur(event) {				
			if (this.tagName == 'FONT')
				this.tagName = '';				
		},
					
		keydown(event) {				
			var self = event.target;
			var key = event.key;

			if (self.nodeName == 'INPUT') {
				switch (key) {
					case 'Enter':
					case 'Tab':
						console.log("self.parentElement.focus();");
						self.parentElement.focus();
					default:
						break;
				}
				return;
			}

			switch (key) {
				case 'ArrowLeft':
					var previousElementSibling = self.previousElementSibling;
					if (previousElementSibling == null || previousElementSibling.tagName == 'BR'){
						if (self.className == 'theorem') {
							previousElementSibling = self.parentElement.parentElement.querySelector('.package:last-of-type');
						}							
					}

					previousElementSibling.focus();
					break;
				case 'ArrowRight':
					var nextElementSibling = self.nextElementSibling;
					if (nextElementSibling == null && self.className == 'package') {
						nextElementSibling = self.parentElement.parentElement.querySelector('.theorem');
					}
					nextElementSibling.focus();
					break;
				case 'ArrowDown':
					var offsetTop = self.offsetTop;
					var current = self;						
					for(;;){
						var current = current.nextElementSibling;
						if (current == null){
							if (self.className == 'package'){
								current = self.parentElement.parentElement.querySelector('.theorem'); 
								break;
							}
							return;
						}
						
						if (current.offsetTop > offsetTop){								
							break;
						}
					}
					
					var offsetLeft = self.offsetLeft;
					for(;;){
						if (current.offsetLeft < offsetLeft){
							var nextElementSibling = current.nextElementSibling;
							if (nextElementSibling == null){
								break;
							}
							current = nextElementSibling;
						}
						else
							break;
					}
					
					current.focus();
					event.preventDefault();
					break;
				case 'ArrowUp':
					var offsetTop = self.offsetTop;						
					var current = self;						
					for(;;){
						var current = current.previousElementSibling;
						if (current.tagName == 'BR'){
							if (self.className == 'theorem'){
								current = self.parentElement.parentElement.querySelector('.package:last-of-type'); 
								break;
							}								
							return;
						}								
						
						if (current.offsetTop < offsetTop){								
							break;
						}
					}
					
					var offsetLeft = self.offsetLeft;
					for(;;){
						if (current.offsetLeft > offsetLeft){
							current = current.previousElementSibling;
						}
						else
							break;
					}
					
					current.focus();
					event.preventDefault();
					break;	
				case 'Home':
					var current = self.parentElement.parentElement.querySelector('.package');
					if (current == null){
						current = self.parentElement.parentElement.querySelector('.theorem');
					}
					current.focus();
					break;						
				case 'End':
					var current = self.parentElement.parentElement.querySelector('.theorem:last-of-type');
					if (current == null){
						current = self.parentElement.parentElement.querySelector('.package:last-of-type');
					}
					current.focus();
					break;
				case 'F2':
					this.rename();						
					break;
				case 'Enter':
					this.dblclick(event);
					break;
				case 'Delete':
					this.remove();
					break;
				case 'Backspace':
					var search = location.search;
					var index = search.lastIndexOf('.', search.length - 2);
					if (index < 0)
						index = search.lastIndexOf('/', search.length - 2);
					
					if (index > 0){
						var hash = search.endsWith('.') || search.endsWith('/')?
								search.slice(index + 1, -1):
									search.slice(index + 1);
						
						location.hash = hash;
						location.search = search.substring(0, index + 1);
					}
					break;
				default:
					if (key.length == 1) {
						var currentTime = new Date().getTime();
						console.log("currentTime = " + currentTime);
						console.log("previousTime = " + previousTime);
						if (previousKey && currentTime - previousTime < 256){
							key = previousKey + key;
						}
						
						console.log("key = " + key);
						
						var startFromScratch = 2;
						for (; ;) {
							if (self.nextElementSibling == null) {
								if (!startFromScratch)
									break;
								if (self.className == 'package') {
									self = self.parentElement.parentElement.querySelector('.theorem');
									--startFromScratch;
									if (self == null){
										self = event.target;
										self = self.parentElement.parentElement.querySelector('.package');
										--startFromScratch;											
									}
								}
								else if (self.className == 'theorem') {
									self = self.parentElement.parentElement.querySelector('.package');
									--startFromScratch;
								}
							}
							else
								self = self.nextElementSibling;

							if (self.textContent.trim().match(eval(`/^${key}/i`))) {
								self.focus();
								break;
							}
						}
						
						previousKey = key;
						previousTime = currentTime;

						return;
					}
					break;
			}
			
			if (previousKey)
				previousKey = '';
		},

		indexFocused() {
			var self = this.$parent;				
			return self.$parent.indexOf(self);
		},
		
		contextmenu(event) {
			//console.log("contextmenu: function(event)");
			var self = event.target;				
			
			var parent = this.$parent.$parent;
			
			parent.left = event.x + self.getScrollLeft();
			parent.top = event.y + self.getScrollTop();
			
			parent.focusedIndex = this.indexFocused();
			
			setTimeout(()=>{
				// Code that will run only after the entire view has been rendered					
				self.nextElementSibling.focus();					
			}, 100);
		},
		
		rename() {
			var self = this.$el;
			this.tagName = 'INPUT'; 
			this.$nextTick(() => {							
				// Code that will run only after the entire view has been rendered
				console.log('self.lastElementChild = ');						
				console.log(self.lastElementChild);							
				console.log(self.lastElementChild.value);
				self.lastElementChild.focus();
			});
		},
		
		remove() {	
			this.visible = false;
			this.$parent.remove();
		},
		
		blur_input(event){
			var text = event.target.value;
			
			console.log('oldText = ' + this.text);
			console.log('newText = ' + text);
			var className = this.$parent.$el.className;
			
			var search = location.search;
			var folder = location.search.slice(8);
			console.log('folder = ' + folder);

			if (folder.indexOf('/') >= 0)
				folder = folder.replaceAll('/', '.');
			
			if (folder.endsWith('.'))
				folder = folder.slice(0, -1);
			
			var sympy = axiom_user();
			
			var self = this.$parent;
			var data = {};
			
			data['old'] = this.text;
			data['new'] = text;
			if (folder)
				folder += '.';
			data['package'] = folder;

			form_post(`/${sympy}/php/request/rename.php`, data).then(res => {
				console.log('res = ' + res);
				
				if (text.indexOf('.') >= 0){
					var index = text.lastIndexOf('.');
					var subPackage = text.substring(0, index);
					
					if (search.indexOf('/') >= 0){
						subPackage = subPackage.replaceAll('.', '/');
						if (!search.endsWith('/')){
							subPackage = '/' + subPackage;
						}
						location.search += subPackage;
					}
					else{
						if (!search.endsWith('.')){
							subPackage = '.' + subPackage;
						}
						location.search += subPackage;							
					}
				}
				else if (!text){						
					var parent = self.$parent;
					parent.remove(parent.children.indexOf(self));						
				}
			});
			
			var texts = this.$root[className + 's'];
			var index = texts.indexOf(this.text);
			texts[index] = text;
			this.tagName = '';
		},
		
		change_input(event){
			console.log("change_input(event){");
		}
	}
}
</script>

<style scoped>
div>font {
	background: #00BFFF;
}

div>input {
	background-color: rgb(199, 237, 204);
	font-style: inherit;
	font-size: inherit;
	font-weight: inherit;
	font-family: inherit;
}

div {
	cursor: pointer;
	caret-color: transparent;
}
</style>