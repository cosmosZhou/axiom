<template>
	<li>
		<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
	</li>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownLI.vue');

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
		'MarkdownUL',
		'MarkdownOL',
		'MarkdownSPAN',
	],
	props,

    data: {
    },

    computed: {
    },

	directives: {
	}
});


</script>

<style>
</style>
