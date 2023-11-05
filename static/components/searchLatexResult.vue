<template>
	<searchForm :keyword=latex :latex=true :regularExpression=false :wholeWord=false :caseSensitive=false></searchForm>
	latex in search:
	<p v-text="`\\[${latex}\\]`"></p>
	search results:
	<br>
	in all, there are {{list.length}} hits:
	<br>
	<ul>
    	<li v-for="result of list">
    		similarity = {{result.similarity}}, id = <a :href="`query.php?user=user&from[axiom]=MathIR&id=${result.id}`" target="searchResult">{{result.id}}</a>
			<p v-text="`\\[${result.latex}\\]`"></p>
    	</li>
	</ul>
</template>

<script>
console.log('import searchLatexResult.vue');
import searchForm from "./searchForm.vue"
//import searchLink from "./searchLink.vue"

export default {
	components: {searchForm},

	props : ['list', 'latex'],

	async created() {
		console.log(this.list);
		console.log(this.latex);
		for (var obj of this.list) {
			var {id} = obj;
			var [{latex}] = await query('localhost', 'user', null, `select latex from axiom.MathIR where id = ${id}`);
			obj.latex = latex;
		}
	},

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