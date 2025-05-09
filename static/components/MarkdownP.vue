<template>
    <p>
        <component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
    </p>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownP.vue');

const props = defineProps({
    args: Array,
    kwargs: Object,
});

const self = new Vue({
    components: [
        'MarkdownText', 
        'MarkdownBracket',
        'MarkdownA',
        'MarkdownB', 
        'MarkdownI',
        'MarkdownLatex',
        'MarkdownUL',
        'MarkdownOL',
    ],
	props,

    data: {
    },

    computed: {
    },

    mounted() {
    },
});
</script>
<style>
</style>
