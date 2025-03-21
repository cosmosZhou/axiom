<template>
    <textarea name=apply>{{text}}</textarea>
</template>

<script>
import codeMirror from "./codeMirror.vue"
console.log('import renderApply.vue');

export default {
    props : [ 'text'],
    
    created() {
    	var hash = location.hash;
    	if (hash){
    		this.hash = hash.slice(1);	
    	}
    },
    
    updated() {
    },
    
    computed: {
    	user: codeMirror.computed.user,
    	module: codeMirror.computed.module,
        
    	firstSibling() {
            return this;                
        },
        
        nextSibling() {
            return this.$parent.renderLean[0];
        },
        
        lastSibling() {
            var prove = this.$parent.renderLean;
            return prove[prove.length - 1];                
        },        
    },
    
    data() {
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