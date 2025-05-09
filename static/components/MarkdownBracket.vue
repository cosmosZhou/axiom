<template>[<component :is=self.components[self.text.func] v-bind=self.text.bind />]</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownBracket.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components: [
		'MarkdownText',
	],
	props,

    data: {
    },

    computed: {
		text() {
			return self.args[0];
		},
    },

	directives: {
	}
});
</script>

<style>
</style>
