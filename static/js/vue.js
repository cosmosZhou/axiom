import { ref, computed, getCurrentInstance, onMounted, defineAsyncComponent } from 'vue'


class Component {
	defineProperty(data, key, $emit = null) {
		var attributes = $emit?
			{
				get() {
					return data[key];
				},
				set(value) {
					$emit(`update:${key}`, value);
				},
			}:
			{
				get() {
					return data[key].value;
				},
				set(value) {
					data[key].value = value;
				},
			};
		attributes.enumerable = true;
		attributes.configurable = true;
		Object.defineProperty(this, key, attributes);
	}
}

class Parent extends Component {
	constructor() {
		super();
		// fetch exposed data from `defineExpose(self.$expose)`;
		const {parent : {exposed}} = getCurrentInstance();
		for (let key in exposed) {
			this.defineProperty(exposed, key);
		}
	}
}

class Vue extends Component {
	constructor(vue) {
		super();
		const {data, refs, computed: $computed, props, $emit, directives, components, mounted} = vue;
		var $expose = {};
		if (data) {
			const $data = {};
			for (const key in data) {
				$data[key] = ref(data[key]);
				this.defineProperty($data, key);
				$expose[key] = $data[key];
			}
			this.$data = $data;
			$expose['$data'] = $data;
		}
		if (refs) {
			const $refs = {};
			for (const key in refs) {
				$refs[key] = ref(refs[key]);
				this.defineProperty($refs, key);
			}
			this.$refs = $refs;
			$expose['$refs'] = $refs;
		}
		if (computed) {
			for (const key in $computed) {
				$computed[key] = computed($computed[key]);
				this.defineProperty($computed, key);
				$expose[key] = $computed[key];
			}
			this.$computed = $computed;
		}
		if (props) {
			var emit = $emit?? ((event, value) => {
				console.log(`emit ${event} = ${value} is not defined`);
			});
			const $props = {};
			for (const key in props) {
				$props[key] = props[key];
				this.defineProperty($props, key, emit);
				$expose[key] = $props[key];
			}
			this.$props = $props;
		}
		this.$expose = $expose;
		// Handle directives registration
		if (directives) {
			const instance = getCurrentInstance();
			if (instance) {
				// Merge the component's existing directives with new ones
				instance.type.directives = {
					...(instance.type.directives || {}),
					...directives,
				};
			}
		}

		if (components) {
			this.components = components.isArray?
				components.reduce((acc, name) => {
					acc[name] = (name => defineAsyncComponent(() => import(`../components/${name}.vue`)))(name);
					return acc;
				}, {}) :
				components;
		}

		if (mounted) {
			onMounted(() => {
				mounted();
			});
		}
	}

	get $parent() {
		if (!this.$$parent)
			this.$$parent = new Parent();
		return this.$$parent;
	}
}

console.log('import vue.js');

export default Vue;
