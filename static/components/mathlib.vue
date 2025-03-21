<template>
	<lemma :name=name :instImplicit=instImplicit :strictImplicit=strictImplicit :implicit=implicit :given=given :explicit=explicit :imply=imply :index=0 @keydown=keydown></lemma>
</template>

<script>
import lemma from "./lemma.vue"
import { mounted, click_left } from "../js/lemma.js"

console.log('import mathlib.vue');

export default {
	components: {
		lemma
		// 'console': () => import('./console.vue'),
	},
	props : [ 'name', 'type', 'instImplicit', 'strictImplicit', 'implicit', 'given', 'explicit', 'imply'],
	
	created() {
	},

	data() {
		return {
			open_sections: [],
			sections: [],
			renderLean : {},
			selectedIndex: [],
		};
	},

	computed: {
		lemma() {
			return [this.$parent.$data];
		},

        leanFile() {
            return this.type;
        },
	},
	
	methods: {
        click_left,
		async keydown(event) {
			switch (event.key) {
			case 'F5':
				await this.build();
				event.preventDefault();
				break;
			}
		},

		async build() {
			var {name} = this;
			var {type, instImplicit, strictImplicit, implicit, given, default: explicit, imply} = await form_post('php/request/mathlib.php', {name});
			Object.assign(this.$parent.$data, {type, instImplicit, strictImplicit, implicit, given, explicit, imply});
            var sql = `
replace into 
    axiom.mathlib
    (name, type, instImplicit, strictImplicit, implicit, given, \`default\`, imply) 
    values (
        ${name.mysqlStr()},
		${type.mysqlStr()},
        ${instImplicit? instImplicit.mysqlStr(): null},
        ${strictImplicit? strictImplicit.mysqlStr(): null},
        ${implicit? implicit.mysqlStr(): null},
        ${given? JSON.stringify(given).mysqlStr(): null},
        ${explicit? explicit.mysqlStr(): null},
        ${JSON.stringify(imply).mysqlStr()}
    )
`;
            console.log(sql);
            var rowcount = await form_post('php/request/execute.php', {sql});
            console.log("rowcount =", rowcount);
		},
	},
	
	mounted() {
		var {imply, type} = this;
		if (!type || !imply.lean || !imply.latex)
			this.build();

		mounted(this);
	},
}
</script>

<style>
</style>