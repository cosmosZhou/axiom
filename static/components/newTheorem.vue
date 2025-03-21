<template>
	module :
	<newInput ref=newInput :module=module></newInput>
	<render ref=render :imports=imports :open=open :lemma=lemma :error=error :module=module :date=date></render>
</template>

<script>
import render from "./render.vue"
import newInput from "./newInput.vue"
console.log('import newTheorem.vue');

export default {
	components: { render, newInput },
	props : [ 'imports', 'open', 'lemma', 'error', 'date'],
	
	data() {
		var module = getParameterByName('new');
		var module = module.replace(/[/\\]/g, '.');
		return {
			module
		};
	},
	
	computed: {
		renderLean() {
   			var proof = [];
   			proof.push(this.$refs.proof);
   			return proof;
   		},
   		
   		newInput() {
   			return this.$refs.newInput;
   		},
   		
   		user() {
   			return axiom_user();	
   		},
   		
   		action() {
   			var module = this.module.replace(/\./g, '/');
   			return `/${this.user}/?module=${module}`;
   		},
	},
	
	methods: {
		update_action() {
			this.$refs.render.action = this.action;
		},
	},
}
</script>

<style>
</style>