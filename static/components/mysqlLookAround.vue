<template>
	<template v-if=look_behind[Field]>
		(<select :name=look_behind_operator_name :value=operator.look_behind[Field] @input=input_operator @keydown=keydown_select_look_behind>
			<option v-for="op of ['=', '!']" :value=op>{{'?<' + op}}</option>
		</select>
		<input v-listen type=text class=look-around :name=look_behind_value_name :size=look_behind[Field].length v-model=look_behind[Field] @keydown=keydown_look_behind />)
	</template>
	<input v-focus type=text :name=value_name(Field) @change=change_input v-model=kwargs[Field] :style=style_input(Field) @keydown=keydown />
	<template v-if=look_ahead[Field]>
		(<select :name=look_ahead_operator_name :value=operator.look_ahead[Field] @input=input_operator @keydown=keydown_select_look_ahead>
			<option v-for="op of ['=', '!']" :value=op>{{'?' + op}}</option>
		</select>
		<input v-listen type=text class=look-around :name=look_ahead_value_name :size=look_ahead[Field].length v-model=look_ahead[Field] @keydown=keydown_look_ahead />)
	</template>
</template>

<script>

console.log('import mysqlLookAround.vue');

export default {
	components: {},

	props : ['Field'],

	data() {
		return this.$parent.$data;
	},

	created() {
	},

	computed: {
		operator_value() {
			return this.$parent.operator_value;
		},

		primary_key() {
			return this.$parent.primary_key;
		},

		style_input() {
			return this.$parent.style_input;
		},

		kwargs() {
			return this.$parent.kwargs;
		},

		change_input() {
			return this.$parent.change_input;
		},

		operator() {
			return this.$parent.operator;
		},

		value_name() {
			return this.$parent.value_name;
		},

		input_operator() {
			return this.$parent.input_operator;
		},

		look_behind() {
			return this.$parent.look_behind;
		},

		look_ahead() {
			return this.$parent.look_ahead;
		},

		look_behind_operator_name() {
			var {Field, primary_key} = this;
			if (primary_key)
				return `operator[look_behind]${primary_key}[${Field}]`;

			return `operator[look_behind][${Field}]`;
		},

		look_ahead_operator_name() {
			var {Field, primary_key} = this;
			if (primary_key)
				return `operator[look_ahead]${primary_key}[${Field}]`;

			return `operator[look_ahead][${Field}]`;
		},

		look_behind_value_name() {
			var {Field, primary_key} = this;
			if (primary_key)
				return `look_behind[${primary_key}][${Field}]`;

			return `look_behind[${Field}]`;
		},

		look_ahead_value_name() {
			var {Field, primary_key} = this;
			if (primary_key)
				return `look_ahead[${primary_key}][${Field}]`;

			return `look_ahead[${Field}]`;
		},

	},

	methods: {
		keydown_select_look_behind(event) {
			switch (event.key) {
			case 'ArrowRight':
				event.target.nextElementSibling.focus();
				event.preventDefault();
				break;
			}
		},

		keydown_look_behind(event) {
			switch (event.key) {
			case 'ArrowLeft':
				var input = event.target;
				if (!input.selectionStart && !input.selectionEnd) {
					input.previousElementSibling.focus();
				}
				break;
			case 'ArrowRight':
				var input = event.target;
				var {length} = input.value;
				if (input.selectionStart == length && input.selectionEnd == length) {
					input.nextElementSibling.focus();
				}
				break;
			}
		},

		keydown_select_look_ahead(event) {
			switch (event.key) {
			case 'ArrowLeft':
				var select = event.target;
				select.previousElementSibling.focus();
				event.preventDefault();
				break;
			case 'ArrowRight':
				var select = event.target;
				select.nextElementSibling.focus();
				event.preventDefault();
				break;
			}
		},

		keydown_look_ahead(event) {
			switch (event.key) {
			case 'ArrowLeft':
				var input = event.target;
				if (!input.selectionStart && !input.selectionEnd) {
					input.previousElementSibling.focus();
				}
				break;
			}
		},

		keydown(event) {
			switch (event.key) {
			case 'ArrowLeft':
				var input = event.target;
				if (!input.selectionStart && !input.selectionEnd) {

					var {name} = input;
					if (!this.operator_value[name] || !this.operator_value[name].match(/regexp/))
						break;

					var {look_behind} = this.kwargs;
					if (!look_behind) {
						look_behind = {};
						this.kwargs.look_behind = look_behind;
					}

					if (look_behind[name]) {
						input.previousElementSibling.focus();
					}
					else {
						look_behind[name] = '.*';//(?<=.*) or (?<!.*);
						if (!this.operator.look_behind)
							this.operator.look_behind = {};

						if (!this.operator.look_behind[name])
							this.operator.look_behind[name] = '=';

						this.$nextTick(() => {
							input.previousElementSibling.focus();
						});
					}
				}
				break;
			case 'ArrowRight':
				var input = event.target;
				var {length} = input.value;
				if (input.selectionStart == length && input.selectionEnd == length) {
					var {name} = input;
					if (!this.operator_value[name] || !this.operator_value[name].match(/regexp/))
						break;

					if (this.operator_value[name] == 'regexp_like') {
						if (!this.operator.regexp_like)
							this.operator.regexp_like = {};

						if (!this.operator.regexp_like[name])
							this.operator.regexp_like[name] = 'c';

						this.$nextTick(() => {
							input.nextElementSibling.focus();
						});
					}
					else {
						var {look_ahead} = this.kwargs;
						if (!look_ahead) {
							look_ahead = {};
							this.kwargs.look_ahead = look_ahead;
						}

						if (look_ahead[name]) {
							input.nextElementSibling.nextElementSibling.focus();
						}
						else {
							look_ahead[name] = '.*';//(?=.*) or (?!.*) ;
							if (!this.operator.look_ahead)
								this.operator.look_ahead = {};

							if (!this.operator.look_ahead[name])
								this.operator.look_ahead[name] = '=';

							this.$nextTick(() => {
								input.nextElementSibling.nextElementSibling.focus();
							});
						}
					}
				}
				break;
			}
		},

	},

	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	if (!location.hash) {
		    		var self = binding.instance;
		    		var mysql = self.$parent.$parent.$parent;
		    		if (mysql.focus != false)
		    			el.focus();
		    	}
		    },
		},

		listen: {
		    // after dom is inserted into the document
		    beforeUnmount(el, binding) {
		    	do {
		    		if (el.nextElementSibling)
		    			el = el.nextElementSibling;
		    		else {
		    			el = el.parentElement.nextElementSibling.querySelector('input');
		    			break;
		    		}
		    	}
		    	while (el.tagName != 'INPUT');

	    		el.focus();
		    },
		},
	},
}
</script>

<style>

input.look-around:focus{
	outline: none;
}

input.look-around{
	border: none;
}

</style>