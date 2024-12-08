<template>
	<searchForm ref=searchForm :keyword=keyword :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive :replacement=replacement :limit=limit @keydown=keydown></searchForm>
	search results:
	<br>
	in all, there are {{list.length}} hits:
	<br>
	<ul>
    	<li v-for="module, i of list">
    		<searchLink :module=module :ref="el => searchLink[i] = el"></searchLink>
    	</li>
	</ul>
</template>

<script>
console.log('import searchResult.vue');
import searchForm from "./searchForm.vue"
import searchLink from "./searchLink.vue"

export default {
	components: {searchForm, searchLink},

	props : ['list', 'keyword', 'caseSensitive', 'wholeWord', 'regularExpression', 'replacement', 'limit'],

	data(){
		return {
			searchLink: [],
		};
	},

	computed: {
	},

	methods: {
		keydown(event) {
			switch (event.key) {
			case 'h':
				if (!event.ctrlKey)
					break;
				
				console.log('ctrl+H for replacement');
				setAttribute(this, 'replacement', this.replacement == null? '' : null);
				event.preventDefault();
				break;
			}
		},

		async replace(event) {
			var {searchLink: [searchLink]} = this;
			await searchLink.replace();
			this.list.shift();
			this.$nextTick(() => {
				if (this.list.length)
					this.searchLink[0].focus();
			});
		},

		async replaceAll(event) {
			while (this.list.length)
				await this.replace();
		},
	},		
}

</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>