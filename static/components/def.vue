<template>
    <div class=def>
        <renderLean :text=lean :index="[index]"></renderLean>
    </div>
</template>

<script>
import renderLean from "./renderLean.vue"
console.log('import def.vue');

export default {
    components: { renderLean },
    props : [ 'lean', 'index'],
    
    created() {
    },
    
    data() {
        return {
            postname: 'def',
        };
    },
    
    computed: {
        renderLean() {
            return this.$parent.renderLean;
        },
    },

    updated() {
    },
    
    mounted() {
    },

    methods: {
        click_left() {

        },
    },
    
    directives: {
    },
};

</script>

<style>
div.def .cm-s-indent {
	margin-left: -0.2em;
}

div.def {
    margin-bottom: 1em;
}
</style>