<template>
    <component v-if=self.is_void :is=self.name v-bind="self.bind"/>
    <component v-else :is=self.name v-bind="self.bind">
        <component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
    </component>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownTag.vue');

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
        'MarkdownP', 
        'MarkdownLatex',
        'MarkdownUL',
        'MarkdownOL',
        'MarkdownTag', 
        'MarkdownSPAN', 
    ],
	props,

    data: {
    },

    computed: {
        is_void() {
            return self.kwargs.is_void;
        },

        name() {
            return self.kwargs.name;
        },

        bind() {
            return self.kwargs.bind;
        }
    },

    mounted() {
    },
});
</script>
<style>
think {
    /* Grey text */
    color: #666;
    /* Smaller font */
    font-size: 0.9em;
    /* Optional background */
    background: #f5f5f5;
    /* Optional spacing */
    padding: 8px;
    /* Optional rounded corners */
    border-radius: 4px;
    display: inline-block;
    margin: 4px 0;
}
</style>
