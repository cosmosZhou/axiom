<template>
	<div>
		<MarkdownDocument :args=root.args />
	</div>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownDocument from "./MarkdownDocument.vue"
// console.log('import markdown.vue');

const props = defineProps({
	root : Object,
});

const self = new Vue({
	props,

    data: {
    },

	computed : {
	},

	directives: {
	},

	mounted() {
	}
});

</script>
<style>
</style>
