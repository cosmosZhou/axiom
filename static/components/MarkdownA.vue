<template>
	<a :href=self.href>
		<component :is=self.components[self.text.func] v-bind=self.text.bind />
	</a>
</template>

<script setup>
import Vue from "../js/vue.js"
console.log('import MarkdownA.vue');

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
		href() {
			return 'http://' + self.args[1].toString();
		},

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
