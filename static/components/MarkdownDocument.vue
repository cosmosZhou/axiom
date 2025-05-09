<template>
	<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownDocument.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components: [
		'MarkdownText', 
		'MarkdownBracket',
		'MarkdownA',
		'MarkdownB',
		'MarkdownI',
		'MarkdownH',
		'MarkdownP',
		'MarkdownSPAN',
		'MarkdownUL',
		'MarkdownOL',
		'MarkdownTABLE',
		'MarkdownCODE',
		'MarkdownTag', 
	],
	props,

    data: {
    },

    computed: {
    },

	directives: {
	},

	mounted() {
	},
});
</script>

<style>
</style>
