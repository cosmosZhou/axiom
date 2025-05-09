<template>
    <table border=1>
        <component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
    </table>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownTABLE.vue');

const props = defineProps({
	args: Array,
    kwargs: Object,
});

const self = new Vue({
    components: ['MarkdownTR'],
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
