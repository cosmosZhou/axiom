<template>
    <div class=lemma>
        <template v-if=comment>
            <span class=green>-- </span><input class=green :name="`lemma[${index}][comment]`" v-model=comment :size="comment.length + 1" />
            <br>
        </template>
        <template v-if=attribute>
            <input type=hidden :name="`lemma[${index}][attribute]`" :value=JSON.stringify(attribute) />
            <span class=orange>@[</span><span class=blue>{{ attribute.join(", ") }}</span><span class=orange>]</span><br>
        </template>

        <select v-if=accessibility :name="`lemma[${index}][accessibility]`" :value=accessibility :style=style_select(accessibility)>
            <option v-for="value of accessibilities" :value=value>{{value}}</option>
        </select>

        <span v-clipboard class=blue :data-clipboard-text=leanFile>lemma</span> <input class=orange :name="`lemma[${index}][name]`" :value=name :size="name.length + 1" />
        {{ instImplicit || strictImplicit || implicit || given || explicit? '': ':'}}
        <renderLean v-if=instImplicit :text=instImplicit :index="[index, 'instImplicit']"></renderLean>
        <renderLean v-if=strictImplicit :text=strictImplicit :index="[index, 'strictImplicit']"></renderLean>
        <renderLean v-if=implicit :text="given || explicit? implicit: implicit + ' :'" :index="[index, 'implicit']"></renderLean>

        <div v-if=given>
            <hr>
            <span v-clipboard class=green :data-clipboard-text=module :index=index><b>-- given</b></span>
            <div v-for="given, i of given" @keydown=keydown @click.left.stop=click_select :index=i :class="class_given(i)" tabindex="1000">
                <renderLean v-if=given.insert :text=given.lean :index="[index, 'given', i]"></renderLean>
                <template v-else>
                    <p v-latex.block=given.latex></p>
                    <input type=hidden :name="`lemma[${index}][given][${i}]`" :value=given.lean />
                </template>
            </div>
        </div>

        <renderLean v-if=explicit :text=explicit :index="[index, 'explicit']"></renderLean>
        <hr>
        <a style='font-size: inherit' :href="module? `?callee=${module}`: `?q=${name}&fullText=on`" title='callee hierarchy'>
            <span class=green><b>-- imply</b></span>
        </a>
        <div @keydown=keydown @click.left.stop=click_select :class=class_imply tabindex="1000">
            <renderLean v-if=imply.insert :text=imply.lean :index="[index, 'imply']"></renderLean>
            <template v-else>
                <p v-latex.block=imply.latex></p>
                <input type=hidden :name="`lemma[${index}][imply]`" :value=imply.lean />
            </template>
        </div>
        <template v-if=proof>
            <hr>
            <a style='font-size: inherit' :href="`?caller=${module}`" title='caller hierarchy'>
                <span class=green><b>-- proof</b></span>
            </a>

            <template v-for="(code, i) in get_proof_list(proof)" :key=refresh>
                <renderLean :text=code.lean :index="get_index(index, i)"></renderLean>
                <p v-latex.block=gather(code.latex)></p>
                <span v-if=code.think v-html=code.think v-clipboard></span>
            </template>
        </template>
    </div>
</template>

<script>
import renderLean from "./renderLean.vue"
import { fetch_code } from "../js/lemma.js"
console.log('import lemma.vue');
const accessibilities = ['public', 'protected', 'private'];

export default {
    components: { renderLean },
    props : [ 'comment', 'attribute', 'accessibility', 'name', 'instImplicit', 'strictImplicit', 'implicit', 'given', 'explicit', 'imply', 'proof', 'index'],
    
    created() {
    },
    
    data() {
        return {
            accessibilities,
        };
    },
    
    computed: {
        lemma() {
            return this.$parent.lemma[this.index];
        },

        click_left() {
            return this.$parent.click_left;
        },
        
        module() {
            return this.$parent.module;
        },

        sections() {
            return this.$parent.sections;
        },

        renderLean() {
            return this.$parent.renderLean;
        },

        refresh: {
            get() {
                return this.$parent.refresh;
            },
            set(value) {
                this.$parent.refresh = value;
            },
        },

        selectedIndex() {
            return this.$parent.selectedIndex;
        },

        class_imply() {
            return this.selectedIndex.equals([this.index, 'imply'])? 'focus': '';
        },

        regexp_section() {
            return new RegExp(this.sections.join('|'));
        },

        open_lemma_sections() {
            var section = [];
            for (var open of this.$parent.open_sections) {
                if (open.fullmatch(this.regexp_section))
                    section.push(open);
            }
            return section;
        },

        leanFile() {
            return this.$parent.leanFile;
        },
    },

    updated() {
    },
    
    mounted() {
    },

    methods: {
        gather(latex) {
            if (latex && latex.isArray) {
                latex = latex.join(' \\\\\n');
                return `\\begin{gather}
${latex}
\\end{gather}`;
            }
            return latex;
        },

        code_generation(code, i) {
            var {index} = this;
            var self = this.$parent;
            var codes = ranged(index).map(i => fetch_code(self.lemma[i]));
            var lemma = self.lemma[index];
            codes.push(fetch_code(lemma, code));
            var {proof} = lemma;
            var by = proof.by ? 'by' : (proof.calc ? 'calc' : '');
            index = [index, 'proof'];
            if (by)
                index.push(by);
            self.code_generation(codes.join("\n\n\n"), ...index, i);
        },

        async Escape(code, indices) {
            delete code.insert;
            var lean = getitem(this.renderLean, ...indices).editor.getValue();
            if (code.lean != lean) {
                code.lean = lean;
                var data = await form_post('php/request/latex.php', {lean});
                if (data) {
                    if (data.isArray) {
                        var [index, attr] = indices;
                        var lemma = this.$parent.lemma[index];
                        if (attr == 'given') {
                            var i = parseInt(indices[2]);
                            for (var j of range(data.length)) {
                                if (j) {
                                    if (data[j].latex) 
                                        lemma.given.insert(i + j, data[j]);
                                    else {
                                        var explicit = ranged(j, data.length).map(j => data[j].lean);
                                        if (lemma.explicit)
                                            explicit.push(lemma.explicit);
                                        lemma.explicit = explicit.join('\n');
                                        break;
                                    }
                                }
                                else
                                    Object.assign(code, data[j]);
                            }
                        }
                        else {
                            lemma.imply = data.pop();
                            var i = 0;
                            for (var j of range(data.length)) {
                                if (data[j].latex) {
                                    if (!lemma.given)
                                        lemma.given = [];
                                    lemma.given.push(data[j]);
                                }
                                else {
                                    var {lean} = data[j];
                                    if (lean.startsWith('[')) {
                                        if (lemma.instImplicit)
                                            lemma.instImplicit += '\n' + lean;
                                        else
                                            lemma.instImplicit = lean;
                                    }
                                    else if (lean.startsWith('{')) {
                                        if (lemma.implicit)
                                            lemma.implicit += '\n' + lean;
                                        else
                                            lemma.implicit = lean;
                                    }
                                    else if (lean.startsWith('(')) {
                                        if (lemma.explicit)
                                            lemma.explicit += '\n' + lean;
                                        else
                                            lemma.explicit = lean;
                                    }
                                }
                            }
                        }
                    }
                    else {
                        var {latex, error} = data;
                        if (latex)
                            code.latex = latex;
                        else if (error)
                            code.latex = error;
                    }
                }
            }
            this.click_left();
        },

        click_select(event) {
            var {target} = event;
            var {index} = this;
            var child = target;
            while (true) {
                parent = child.parentElement;
                if (parent.tagName == 'DIV')
                    break;
                child = parent;
            }

            var i = parent.getAttribute('index');
            if (i == null && child.tagName != 'P')
                return;
            this.$parent.selectedIndex.array_assign(i == null? [index, 'imply']: [index, 'given', i]);
            console.log('click_select(event) in lemma.vue', this.selectedIndex);
        },

        async keydown(event) {
            var {key, target} = event;
            switch (key) {
            case 'Insert':
                var {index, given, imply} = this;
                var div = target;
                while (div.tagName != 'DIV')
                    div = div.parentElement;
                var i = div.getAttribute('index');
                if (i == null) {
                    if (target.tagName == 'TEXTAREA')
                        return;
                    imply.insert = true;
                }
                else
                    given[i].insert = true;
                break;
            case 'Escape':
                var {index, given, imply} = this;
                var leanCode = target.tagName == 'TEXTAREA'? target.parentElement.parentElement: target;
                var div = leanCode.parentElement;
                var i = div.getAttribute('index');
                if (i == null) {
                    if (target.tagName == 'SPAN')
                        return;
                    await this.Escape(imply, [index, 'imply']);
                }
                else if (this.lemma)
                    await this.Escape(given[i], [index, 'given', i]);
                else
                    break;

                // typesetPromise();
                leanCode.remove();
                break;
            case 'Delete':
                var {index, given} = this;
                if (target.tagName == 'TEXTAREA')
                    return;
                var p = target.tagName == 'MJX-CONTAINER'? target.parentElement: target;
                var div = p.parentElement;
                var i = div.getAttribute('index');
                given.delete(i);
                if (given.length == i) {
                    var back = given.back();
                    if (back) {
                        back.lean += ' :';
                        back.latex = back.latex.replace(/(\$\}\\\])$/, ' :$1');
                    }
                    else {
                        var {lemma} = this;
                        delete lemma.given;
                        if (!lemma.explicit) {
                            var key = null;
                            if (lemma.implicit)
                                key = 'implicit';
                            else if (lemma.strictImplicit)
                                key = 'strictImplicit';
                            else if (lemma.instImplicit)
                                key = 'instImplicit';
                            else
                                return;
                            lemma[key] += ' :';
                            this.renderLean[index][key].editor.setValue(lemma[key]);
                        }
                    }
                }
                break;
            case 'F5':
                console.log('F5');
                event.preventDefault();
                break;
            }
        },

        class_given(i){
            return this.selectedIndex.equals([this.index, 'given', i])? 'focus': '';
        },

        style_select(value) {
            return `width: ${value.length / 2 + 0.5}em`;
        },

        get_proof_list(proof) {
            return proof.by?? proof.calc?? proof;
        },

        get_index(index, i) {
            var {proof} = this;
            index = [index, 'proof'];
            var by = proof.by? 'by' : proof.calc? 'calc' : '';
            if (by) {
                index.push(by);
                proof = proof[by];
            }
            if (i < 0)
                i += proof.length;
            index.push(i);
            if (i < proof.length)
                return index;
        },
    },
    
    directives: {
        clipboard,
        latex
    },
};

</script>

<style scoped>

select {
    color: blue;
    outline: none;
    background-color: transparent;
    box-shadow: none;
    border: none;
    padding: 0;

    -webkit-appearance: none;
    -moz-appearance: none;
    appearance: none;    
    font-size: inherit;
    font-family: inherit;
    font-weight: inherit;
    font-style: inherit;
}

div {
    caret-color: transparent;
}

span.blue {
    color: blue;
}

.green {
    color: green;
}

.orange {
    color: orange;
}

div.focus {
    outline: 2px dotted red;
    /* background-color: white; */
}

</style>