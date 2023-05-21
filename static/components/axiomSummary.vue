<template>
	<div tabindex=1 @keydown=keydown>
		the whole math theory is composed of the following sections:
 
		<searchForm v-if="issearch" :keyword=keyword :caseSensitive=caseSensitive :wholeWord=wholeWord :regularExpression=regularExpression :nlp=nlp></searchForm>		
		<ul>
			<li v-for="(content, section) in repertoire">
				<a :href=href_section(section)>
					{{section}}
				</a>
				<ul>
					<li v-for="(axioms, state) in content">
						<font :class=state>
							theorems {{state}}:
						</font>
						<ul>
							<li v-for="axiom in axioms">
								<a :href=href_module(axiom)>
									{{axiom}}
								</a>
							</li>
						</ul>
					</li>
				</ul>
			</li>
		</ul>
		<br>
		in summary, the following is the total count of each state for all theorems:
		<br>
		<table tabindex=align=left border=1>
	
			<tr>
				<th>state</th>
				<th>count</th>
			</tr>
	
			<tr v-for="tuple of state_count_pairs">
				<td><a :href="href_state(tuple.state)">{{tuple.state}}</a></td>
				<td>{{tuple.count}}</td>
			</tr>	
		</table>
		most recent <input size=2 v-model=topk @change=change_input>axioms updated:
		<a v-for="axiom of recentAxioms" :href=href_module(axiom)>
			<p>{{axiom}}</p>
		</a>
		<br>
	</div>
</template>

<script>
console.log('import axiomSummary.vue');
	
import searchForm from "./searchForm.vue"
	
export default {
	components: {searchForm},
	
	props : ['state_count_pairs', 'repertoire'],
	
	computed: {
		user(){
			return axiom_user();
		},	
	},
	
	data(){
		return {
			issearch: false,
			recentAxioms: [],
			topk: 10,
			
			keyword: '',
			caseSensitive: false,
			wholeWord: false, 
			regularExpression: false,
			nlp: false,
		};
	},

	created(){
		this.updateRecentAxioms();
	},
	
	methods: {
		href_section(section) {
			var {user} = this;
			return `/${user}/index.php?module=${section}`;
		},

		href_module(axiom) {
			var {user} = this;
			return `/${user}/index.php?module=${axiom}`;
		},

		href_state(state){
			if (state == 'total'){
				return `/${this.user}/run.py`;
			}
			var {user} = this;
			return `/${user}/index.php?state=${state}`;
		},
	
		keydown(event){
			switch(event.key){
			case 'f':
			case 'F':
				if (event.ctrlKey){
					this.issearch = true;
					event.preventDefault();
				}
			}
		},
		
		async updateRecentAxioms(){
			this.recentAxioms = await get(`php/request/recent.php?top=${this.topk}`);;
		},
		
		change_input(event){
			this.updateRecentAxioms();
		},
	},
	
	mounted(){
		var failed = document.querySelector('a[href$=failed]') || 
		document.querySelector('a[href$=plausible]')  || 
		document.querySelector('a[href$=unproved]') || 
		document.querySelector('a[href$=unprovable]') || 
		document.querySelector('a[href$=slow]');
		if (failed){
			failed.focus();
		}
	},
}
</script>

<style scoped>
table{
	margin-left: 4em;
}

div:focus{
	outline: none;
}

font.slow{
	color: yellow;
}

font.failed{
	color: red;
}

font.unprovable{
	color: green;
}

font.plausible{
	color: red;
}

font.unproved{
	color: purple;
}

</style>