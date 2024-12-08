<template>
	<div>
		module :
		<newInput ref=newInput :module=module></newInput>
		<form name=form enctype=multipart/form-data method=post :action=action>
			<newApply ref=newApply :text=apply></newApply>
			<br>
			<newProve ref=newProve :text=prove></newProve>
		</form>
	</div>
</template>

<script>
console.log('import newTheorem.vue');
import newInput from "./newInput.vue"
import newApply from "./newApply.vue"
import newProve from "./newProve.vue"

export default {
	components: {newInput, newApply, newProve },
	props : [ 'module', 'apply', 'prove'],
	
	data(){
		return {
		};
	},
	
	computed: {
		renderProve(){
   			var prove = [];
   			prove.push(this.$refs.prove);
   			return prove;
   		},
   		
   		newApply(){
   			return this.$refs.newApply;
   		},
   		
   		newProve(){
   			return this.$refs.newProve;
   		},   		
   		
   		newInput(){
   			return this.$refs.newInput;
   		},
   		
   		user(){
   			return axiom_user();	
   		},
   		
   		action(){
   			var module = this.module.replace(/\./g, '/');
   			return `/${this.user}/?module=${module}`;
   		},
	},
	
	methods: {
	},
}
</script>

<style>
</style>