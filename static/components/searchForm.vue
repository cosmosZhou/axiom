<template>
	<form name=search enctype="multipart/form-data" method=post :action=action @keydown=keydown>
		<input v-focus tabindex=1 type=text spellcheck=false name=keyword size=48 :value=keyword placeholder='input a hint in search of a formula/theorem/axiom' @input=input>
		<br>
			 
		<input tabindex=-1 type=checkbox name=caseSensitive :checked=caseSensitive><u>C</u>ase
			
		<input tabindex=-1 type=checkbox name=wholeWord :checked=wholeWord><u>W</u>holeWord
		
		<input tabindex=-1 type=checkbox name=regularExpression :checked=regularExpression>Rege<u>x</u>
		
		<input tabindex=-1 type=checkbox name=latex :checked=latex><u>L</u>aTex
	</form>
</template>

<script>
console.log('import searchForm.vue');
export default {
	props : ['keyword', 'caseSensitive', 'wholeWord', 'regularExpression', 'latex'],

	computed: {
		user(){
			return axiom_user();	
		}, 
		
		action(){
			return `/${this.user}/index.php`;
		},
	},
	
	methods: {
		input(event){
			setAttribute(this, 'keyword', event.target.value);
		},
		
		keydown(event){
			if (event.altKey){
				switch(event.key){
				case 'c':
					setAttribute(this, 'caseSensitive', !this.caseSensitive);
					break;
				case 'w':
					setAttribute(this, 'wholeWord', !this.wholeWord);
					break;
				case 'x':
					setAttribute(this, 'regularExpression', !this.regularExpression);
					break;
				case 'l':
					setAttribute(this, 'latex', !this.latex);
					break;
				}
			}
		},
	},	
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
				el.focus();
		    },
		},
	},
};
</script>

<style scoped>
form[name=search] {
	float: right;
}
</style>