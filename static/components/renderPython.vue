<template>
    <textarea name=python[]>{{text}}</textarea>
</template>

<script>
console.log('import renderPython.vue');
import codeMirror from "./codeMirror.vue";

export default {
    props : [ 'text'],
    
    created(){
    	var hash = location.hash;
    	if (hash){
    		this.hash = hash.slice(1);	
    	}
    },
    
    updated(){
    },
    
    computed: {
    	user: codeMirror.computed.user,
    	module: codeMirror.computed.module,
        
    	firstSibling(){
            return this;                
        },
    },
    
    data(){
        return {
            editor: null,
            theme: 'eclipse',
            focus: true,
            hash: null,
        };
    },
    
    methods: {
    },
    
    mounted: codeMirror.mounted,    
}
</script>

<style>
</style>