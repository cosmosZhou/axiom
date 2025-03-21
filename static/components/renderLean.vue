<template>
    <textarea :name=name>{{text}}</textarea>
</template>

<script>
import codeMirror from "./codeMirror.vue"
console.log('import renderLean.vue');

export default {
    data() {
    },

    props : [ 'text', 'index'],
    
    created() {
        setitem(this.$parent.renderLean, ...this.index, this);
    },
    
    updated() {
    },
    
    computed:{
        click_left() {
            return this.$parent.click_left;
        },
        
        name() {
            return 'lemma' + this.index.map(i => `[${i}]`).join('');
        },
        
    	user: codeMirror.computed.user,
    	module: codeMirror.computed.module,
        
        firstSibling() {
            return this.$parent.renderLean[0];
        },
        
        nextSibling() {
            var {index} = this;
            var self = this.$parent;
            var [i, key] = index;
            switch (key) {
            case 'instImplicit':
                if (self.lemma.strictImplicit) {
                    index = [i, 'strictImplicit'];
                    break;
                }

            case 'strictImplicit':
                if (self.lemma.implicit) {
                    index = [i, 'implicit'];
                    break;
                }

            case 'implicit':
                var {given} = self.lemma;
                if (given) {
                    var hit = false;
                    for (var i of range(0, given.length)) {
                        if (given[i].insert) {
                            index = [i, 'given', i];
                            hit = true;
                            break;
                        }
                    }
                    if (hit)
                        break;
                }

            case 'given':
                var {given} = self.lemma;
                var j = index[2];
                if (given && j + 1 < given.length) {
                    index = [i, 'given', j + 1];
                    break;
                }
                if (self.lemma.explicit) {
                    index = [i, 'explicit'];
                    break;
                }

            case 'explicit':
                if (self.lemma.imply.insert) {
                    index = [i, 'imply'];
                    break;
                }

            case 'imply':
                index = self.get_index(i, 0);
                break;

            case 'proof':
                var _index = self.get_index(i, index.back() + 1);
                if (_index) {
                    index = _index;
                    break;
                }
                ++i;
                var {lemma} = self.$parent;
                if (i == lemma.length) 
                    return;
                if (lemma[i].instImplicit) {
                    index = [i, 'instImplicit'];
                    break;
                }
                if (lemma[i].strictImplicit) {
                    index = [i, 'strictImplicit'];
                    break;
                }
                if (lemma[i].implicit) {
                    index = [i, 'implicit'];
                    break;
                }
                if (lemma[i].given) {
                    index = [i, 'given', 0];
                    break;
                }
                if (lemma[i].explicit) {
                    index = [i, 'explicit'];
                    break;
                }
                index = [i, index.slice(1, -1), 0];
                break;
            }
            return getitem(self.renderLean, ...index);
        },

        previousSibling() {
            var {index} = this;
            var self = this.$parent;
            var [i, key] = index;
            switch (key) {
            case 'proof':
                var j = index.back();
                if (j > 0) {
                    index = [...index.slice(0, -1), j - 1];
                    break;
                }
                if (self.lemma.imply.insert) {
                    index = [i, 'imply'];
                    break;
                }

            case 'imply':
                if (self.lemma.explicit) {
                    index = [i, 'explicit'];
                    break;
                }

            case 'explicit':
                var {given} = self.lemma;
                if (given) {
                    var hit = false;
                    for (var j of range(given.length - 1, -1, -1)) {
                        if (given[j].insert) {
                            index = [i, 'given', j];
                            hit = true;
                            break;
                        }
                    }
                    if (hit)
                        break;
                }

            case 'given':
                var j = index[2];
                if (j > 0) {
                    index = [i, 'given', j - 1];
                    break;
                }
                if (self.lemma.implicit) {
                    index = [i, 'implicit'];
                    break;
                }

            case 'implicit':
                if (self.lemma.strictImplicit) {
                    index = [i, 'strictImplicit'];
                    break;
                }

            case 'strictImplicit':
                if (self.lemma.instImplicit) {
                    index = [i, 'instImplicit'];
                    break;
                }

            case 'instImplicit':
                if (i) {
                    index = self.get_index(i - 1, -1);
                    break;
                }
                return self.$parent.newInput;
            }
            return getitem(self.renderLean, ...index);
        },
        
        lastSibling() {
            var prove = this.$parent.renderLean;
            return prove[prove.length - 1];
        },

        leanFile() {
            return this.$parent.leanFile;
        },
    },
    
    data() {
    	return {
    		editor: null,
    		focus: true,
    		theme: 'eclipse indent',
    		hash: null,
    	};
    },
    
    methods: {
        code_generation(code) {
            var {index} = this;
            var [, key] = index;
            if (key == 'proof') {
                var self = this.$parent;
                var {lemma} = self.$parent;
                var j = index.back();
                var attr = index.slice(0, -1);
                var codes = ranged(j).map(t => getitem(lemma, ...attr, t));
                codes.push({lean: code});
                this.$parent.code_generation(codes, j);
            }
        },
    },
    
    mounted: codeMirror.mounted,
};
</script>

<style>
.cm-s-indent {
	margin-left: 0.9em;
}
</style>