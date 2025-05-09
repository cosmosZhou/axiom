<template>
	<b>
		<component :is=self.components[self.arg.func] v-bind=self.arg.bind />
	</b>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownB.vue');

const props = defineProps({
	args : Array,
	kwargs : Object
});

const self = new Vue({
	components: [
		'MarkdownText',
		'MarkdownBracket',
		'MarkdownA',
		'MarkdownSPAN',
	],
	props,

    data: {
    },

    computed: {
		arg() {
			return self.args[0];
		}
    },

	directives: {
	}
});
</script>

<style>
</style>
