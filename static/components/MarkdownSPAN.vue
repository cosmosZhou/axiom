<template>
    <span>
        <component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
    </span>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownSpan.vue');

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
        // uncommon tags in span
        'MarkdownUL',
        'MarkdownOL',
    ],
	props,

    data: {
    },

    computed: {
    },

    mounted() {
        // console.log('mounted on MarkdownSpan');
        // console.log('kwargs = ', self.kwargs);
    },
});
</script>
<style>
</style>
