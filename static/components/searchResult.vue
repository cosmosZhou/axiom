<template>
	<searchForm :keyword=keyword :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive></searchForm>
	search results:
	<br>
	in all, there are {{list.length}} hits:
	<br>
	<ul>
    	<li v-for="module of list">
    		<searchLink :module=module></searchLink>
    	</li>
	</ul>
</template>

<script>
console.log('import searchResult.vue');
import searchForm from "./searchForm.vue"
import searchLink from "./searchLink.vue"

export default {
	components: {searchForm, searchLink},

	props : ['list', 'keyword', 'caseSensitive', 'wholeWord', 'regularExpression'],

	computed: {
	},

	methods: {
	},		
}

</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>