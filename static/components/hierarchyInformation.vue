<template>
	<div>
		the lemma in question is a
		<a :href="'?' + keyInput + '=' + this.$parent.module + (deep ? '#deep': '')" :title="'show ' + (deep?'deep':'only first-layer') + ' hierarchy'">{{keyInput}}</a>
		in the following hierarchy, would you switch to
		<a :href=href>{{key}}</a> hierarchy?	
	</div>
</template>

<script>
console.log('import hierarchyInformation.vue');	

export default {
	props : [ 'keyInput', 'deep' ],
	computed:{	
		key() {
			return this.keyInput == 'callee'? 'caller': 'callee';
		},
		
		href() { 
			return '?' + this.key + '=' + this.$parent.module;
		},
	},
	
	methods: {
	},
};
</script>

<style>
</style>