<template>
    <div v-finish @click.left.stop=click_left @keydown=keydown>
        <form name=form spellcheck=false enctype="multipart/form-data" method=post :action=action>
            <input type=hidden name=imports :value=JSON.stringify(imports) />
            <input type=hidden name=def :value=JSON.stringify(def) />
            <input type=hidden name=open :value=JSON.stringify(open) />
            <input type=hidden name=date :value=JSON.stringify(date) />
            <lemma v-for="lemma, index in lemma" :comment=lemma.comment :attribute=lemma.attribute :accessibility=lemma.accessibility :name=lemma.name :instImplicit=lemma.instImplicit :strictImplicit=lemma.strictImplicit :implicit=lemma.implicit :given=lemma.given :explicit=lemma.explicit :imply=lemma.imply :proof=lemma.proof :index=index></lemma>
        </form>

        <template v-if="error.length != 0">
            <br><br>
            <h3>Error Information</h3>
        </template>

        <div v-for="(err, index) of error" :title=err.file>
            <h5>{{err.type}}:</h5>
            <p class="pre-wrap warning">{{err.info}}</p>
            <h5>code:</h5>
            <p class="pre-wrap error" @click="click_font(index, err.line)">{{err.code}}</p>
            <hr>
        </div>

        <div class=bottom-right>
            <p>
                <a :href=href_switch><span class=date>Created on {{date.created}}</span></a>
                <br>
                <span v-if=date.updated class=date>Updated on {{date.updated}}</span>
            </p>
        </div>
        
    </div>
</template>

<script>
import lemma from "./lemma.vue"
import { mounted, click_left, fetch_code } from "../js/lemma.js"
import { generate, parse_token } from "../js/prompting.js"
import { postprocess_word } from "../js/markdown.js"
console.log('import render.vue');

export default {
    components: { lemma },
    props : [ 'imports', 'open', 'lemma', 'error', 'module', 'date'],
    
    created() {
    },
    
    data() {
        return {
        	renderLean: [],
            refresh: false,
            action: '',
            sections: ['Algebra', 'Calculus', 'Discrete', 'Geometry', 'Neuro', 'Set', 'Probability'],
            selectedIndex: [],
            model : getParameterByName('model', 'deepseek-r1')
        };
    },
    
    computed: {
        initial_line() {
            var {imports, open} = this;
            return imports.length + open.length;
        },

        regexp_section() {
            return new RegExp(this.sections.join('|'));
        },

        leanFile() {
            var {module} = this;
            if (!module)
                module = getParameterByName('module');
            return `Axiom/${module.replace(/[.]/g, '/')}.lean`;
        },

        open_sections() {
            var sections = [];
            for (var open of this.open) {
                if (open.isArray)
                    sections.push(...open);
            }
            return sections;
        },

        theorem() {
            return this.lemma.back();
        },

        user() {
            return axiom_user();
        },

        hash() {
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        },

        href_switch() {
			var {protocol, host, pathname, search, hash} = location;
            if (pathname == '/lean/')
                pathname = '/py/';
            else if (pathname == '/py/')
                pathname = '/lean/';
			return `${protocol}\/\/${host}${pathname}${search}${hash}`;
        },
    },

    updated() {
    },
    
    mounted() {
        var {module} = this;
        if (!module) {
            var module = getParameterByName('module');
            module = module.replace(/[\/\\]/g, '.');
            this.$parent.$data.module = module;
            this.$props.module = module;
            this.echo(module);
        }
        mounted(this);

        var {hash} = location;
        if (hash){
            var line = parseInt(hash.slice(1));
            if (line) {
                var indices = this.locate(line);
                var line = indices.pop();
                if (line == null) {
                    var [index, attr] = indices;
                    switch (attr) {
                    case 'proof':
                        var a = this.$el.querySelectorAll('a[title="caller hierarchy"]')[index];
                        a.focus();
                        this.select_span(a.firstChild);
                        break;
                    case 'given':
                        var span = this.$el.querySelector(`span.green[data-clipboard-text][index="${index}"]`);
                        this.select_span(span);
                        break;
                    case 'imply':
                        var a = this.$el.querySelectorAll('a[title="callee hierarchy"]')[index];
                        a.focus();
                        this.select_span(a.firstChild);
                        break;
                    case 'name':
                        var input = this.$el.querySelector(`input[name="lemma[${index}][name]"]`);
                        input.focus();
                        input.select();
                        break;
                    case 'attribute':
                        var input = this.$el.querySelector(`input[name="lemma[${index}][attribute]"]`);
                        this.select_span(input.nextElementSibling);
                        break;
                    case 'created':
                        var span = this.$el.querySelector(`a > span.date`);
                        this.select_span(span);
                        break;
                    case 'updated':
                        var span = this.$el.querySelector(`p > span.date`);
                        this.select_span(span);
                        break;
                    }
                }
                else if (!this.select(indices, line)) {
                    var [index, attr] = indices;
                    switch (attr) {
                    case 'imply':
                        this.lemma[index].imply.insert = true;
                        this.$nextTick(() => {
                            this.select(indices, line);
                        });
                        break;
                    case 'given':
                        this.lemma[index].given[indices[2]].insert = true;
                        this.$nextTick(() => {
                            this.select(indices, line);
                        });
                        break;
                    }
                }
            }
        }
    },

    methods: {
        async GetAuthorization() {
            if (this.Authorization)
                return this.Authorization;
            switch (this.model) {
            case 'deepseek-chat':
            case 'deepseek-reasoner':
                var company = 'DeepSeek';
                break;
            default:
                var company = 'MyCompany';
            }
            var Authorization = await form_post('php/request/authorization.php', {company});
            this.Authorization = Authorization;
            return Authorization;
        },

        async code_generation() {
            // array destructuring of arguments
            var [code, ...index] = arguments;
            index.push('think');
            var {imports, open, lemma, error} = this;
            setitem(lemma, ...index, '');
            code = code.rtrim();
            if (error.length) {
                console.log(error);
            }
            var m = code.match(/\n +sorry$/);
            if (!m) {
                m = code.match(/(\n +).+$/);
                code += m[1] + 'sorry';
            }
            var import_statements = [];
            if (imports.length) {
                for (var name of imports) {
                    if (m = name.match(/^Axiom\.(.+)/)) {
                        name = m[1];
                        var sql = `
select 
  *
from 
  lemma
where 
  module = "${name}"
`
                        var lemma = await form_post('php/request/execute.php', {sql, resultType: 1});
                        if (lemma.length) {
                            [lemma] = lemma;
                            lemma = JSON.parse(lemma.lemma);
                            for (var lemma of lemma) {
                                if (lemma.attribute.includes('main')) {
                                    if (lemma.name != 'main')
                                        lemma.name = name + '.' + lemma.name;
                                    else
                                        lemma.name = name;
                                    delete lemma.proof;
                                    m = lemma.imply.lean.match(/(.+) ?:=( ?by| ?calc|$)/);
                                    if (m)
                                        lemma.imply.lean = m[1];
                                    var axiom = fetch_code(lemma);
                                    import_statements.push(axiom);
                                }
                            }
                        }
                    }
                }
            }
            var prelude = code.match(/^  -- \\\[[^\n]+\\\]$/m) ?
                "Now You're given a partially proven lemma where each intermediate proof-step is annotated with its latex representation:":
                "Below is the main lemma in question:";
            open = open.map(name => {
                if (name.isArray) {
                    name = name.join(' ');
                    return `open ${name}`
                }
                [[key, values]] = Object.entries(name);
                values = values.join(' ');
                return `open ${key} (${values})`
            }).join('\n');
            if (import_statements.length) {
                if (open)
                   import_statements.push(open);
                prelude = `\`\`\`lean4
${import_statements.join('\n')}
\`\`\`
The axioms above are actually lemmas that are proven to be true. Their detailed proofs are omitted here for simplicity. They are listed here to help you prove the current lemma.
${prelude}`
            }
            else if (open)
                code = `${open}\n${code}`
            var task = `${prelude}
\`\`\`lean4
${code}
\`\`\`
Please continue the proof and generate the lean4 code to replace the \`sorry\` tactic. If you can't solve the problem all at once, give me only the next proof-step that is workable and helpful for further problem-solving. Please don't duplicate my original code, give me only the newly added code in your final representation in the lean4 code block below:
\`\`\`lean4
-- your new code here
\`\`\`
since this facilitates the proof-checking process.`
            console.log(task);
            this.generate(
                [
                    {role: "system", content: "You are a helpful lean4 proof assistant."},
                    {role: "user", content: task}
                ],
                {
                    model: this.model,
                    Authorization: await this.GetAuthorization(),
                    index: index,
                    id : this.module
                }
            );
        },

    	generate(prompt, kwargs) {
			var {onmessage, onclose} = this;
			var {model, id, Authorization} = kwargs;
			kwargs.status = {};
            var stream = {
                id,

                onmessage(message) {
                    onmessage(message, kwargs);
                },

                onerror(err) {
                    console.log(err);
                },

                onclose() {
                    onclose(kwargs);
                },
            };
			return generate(prompt, model, stream, Authorization);
    	},

		postprocess(text, word, status, postprocess) {
            if (!text)
                word = word.ltrim();
            text = postprocess(text, word, status);
			return text;
		},

		onmessage(message, kwargs) {
			var {id, data} = message;
			var {index, status} = kwargs;
			if (id && data) {
				try{
					// console.log(data);
					var word = parse_token(data);
					if (word) {
						var {lemma} = this;
						setitem(
							lemma,
							...index,
							this.postprocess(
								getitem(lemma, ...index), 
								word,
								status,
								postprocess_word
							)
						);
					}
				}
				catch(err) {
					console.log(message);
					console.log(err);
					throw new Error(err);
				}
			}
		},

		async onclose(kwargs) {
			var {index} = kwargs;
            var lemma = getitem(this.lemma, ...index);
            console.log(lemma);
		},

		keydown(event) {
			switch (event.key) {
			case 'F5':
				this.echo(this.module);
				event.preventDefault();
				break;
			}
		},

        select_span(span) {
            var range = document.createRange();
            range.selectNodeContents(span);
            var selection = window.getSelection();
            selection.removeAllRanges();
            selection.addRange(range);
        },

        select(indices, line) {
            var cm = getitem(this.renderLean, ...indices);
            if (cm) {
                var cm = cm.editor;
                var text = cm.getLine(line);
                var m = text.match(/^\s*/);
                var ch = m[0].length;
                cm.setCursor(line, ch);
                cm.addSelection({ line, ch }, { line, ch: text.length });
                cm.focus();
                return true;
            }
        },

        locate(find) {
            find -= 1;
            var line = this.initial_line;
            for (let index of range(this.lemma.length)) {
                line += 2;
                var lemma = this.lemma[index];
                if (lemma.comment) {
                    ++line;
                    if (find < line)
                        return [index, 'comment', null];
                }

                if (lemma.attribute) {
                    ++line; // @[main]
                    if (find < line)
                        return [index, 'attribute', null];
                }

                ++line; // private lemma main
                if (find < line)
                    return [index, 'name', null];
                var {instImplicit, strictImplicit, implicit, given, explicit} = lemma;
                if (instImplicit) {
                    // instImplicit: [Field α]
                    var line_instImplicit = line;
                    line += instImplicit.split("\n").length;
                    if (find < line)
                        return [index, 'instImplicit', find - line_instImplicit];
                }
                    
                if (strictImplicit) {
                    // strictImplicit: ⦃x : α⦄
                    var line_strictImplicit = line;
                    line += strictImplicit.split("\n").length;
                    if (find < line)
                        return [index, 'strictImplicit', find - line_strictImplicit];
                }
                    
                if (implicit) {
                    // implicit: {x : α}
                    var line_implicit = line;
                    line += implicit.split("\n").length;
                    if (find < line)
                        return [index, 'implicit', find - line_implicit];
                }
                if (given) {
                    ++line; // --given
                    if (find < line)
                        return [index, 'given', null];
                    // given: (h : a = b)
                    for (var i of range(given.length)) {
                        var line_given = line; 
                        line += given[i].lean.split("\n").length;
                        if (find < line)
                            return [index, 'given', i, find - line_given];
                    }
                }
                if (explicit) {
                    // explicit: (left : Bool := false)
                    var line_explicit = line;
                    line += explicit.split("\n").length;
                    if (find < line)
                        return [index, 'explicit', find - line_explicit];
                }

                ++line; // -- imply
                if (find < line)
                    return [index, 'imply', null];
                
                var line_imply = line;
                line += lemma.imply.lean.split("\n").length;
                if (find < line)
                    return [index, 'imply', find - line_imply];

                ++line; // -- proof
                if (find < line)
                    return [index, 'proof', null];
                
                var {proof} = this.lemma[index];
                var attr = proof.by? 'by' : (proof.calc? 'calc' : null);
                proof = proof.by?? proof.calc?? proof;
                for (var i of range(proof.length)) {
                    var line_start = line;
                    line += proof[i].lean.split("\n").length;
                    if (find < line) {
                        var offset = find - line_start;
                        if (attr)
                            return [index, 'proof', attr, i, offset];
                        else
                            return [index, 'proof', i, offset];
                    }
                }
            }

            line += 2;
            return ['date', find < line? 'created' : 'updated', null];
        },

        click_left,

        delete(indices) {
            var [index, attr] = indices;
            switch (attr) {
            case 'instImplicit':
                this.lemma[index].instImplicit = null;
                break;
            case 'strictImplicit':
                this.lemma[index].strictImplicit = null;
                break;
            case 'implicit':
                this.lemma[index].implicit = null;
                break;
            case 'given':
                var j = indices[2];
                this.lemma[index].given.delete(j);
                break;
            case 'explicit':
                this.lemma[index].explicit = null;
                break;
            case 'imply':
                this.lemma[index].imply = null;
                break;
            case 'proof':
                var proof = this.lemma[index].proof;
                if (indices.length == 4) {
                    proof = proof[indices[2]];
                    var i = indices[3];
                }
                else {
                    var i = indices[2];
                }
                proof.delete(i);
                break;
            }
        },

        async echo(module){
            var code = await form_post('php/request/echo.php', {module});
            console.log(JSON.stringify(code, null, "\t"));
            var {imports, open, def, lemma, error, date} = code;
            this.lemma.array_assign(lemma);
            this.error.array_assign(error);
            this.refresh = true;
            var {user} = this;
            var sql = `
replace into 
    axiom.lemma
    (user, module, imports, open, def, lemma, error, date) 
    values (
        '${user}',
        '${module}',
        ${JSON.stringify(imports).mysqlStr()},
        ${JSON.stringify(open).mysqlStr()},
        ${JSON.stringify(def).mysqlStr()},
        ${JSON.stringify(lemma).mysqlStr()},
        ${JSON.stringify(error).mysqlStr()},
        ${JSON.stringify(date).mysqlStr()}
    )
`;
            console.log(sql);
            var rowcount = await form_post('php/request/execute.php', {sql});
            console.log("rowcount =", rowcount);
        },

        click_font(index, line) {
        	console.log(`index = ${index}, line = ${line}`);
        	var error = this.error[index];
        	switch(error.func){
        	case 'prove':
                var line = this.error.line;
                var sum = 0;
                
                console.log("this.renderLean.length = " + this.renderLean.length);
                for (let cm of this.renderLean) {
                    cm = cm.editor;
                    var _sum = sum;
                    sum += cm.lineCount();
                    if (sum > line) {
                        cm.focus();
                        cm.setCursor(line - _sum, 0);
                        break;
                    }
                }
            	break;
        	case 'apply':
                console.log(error);
                var module = error.file.match(/Axiom\.([\w.]+)/)[1];
                if (module == this.module) {
                }
                else{
                    var href = location.href;
                    href = href.match(/(.+\/(index.php)?\?module=).+/)[1]
                    href += `${module}#${line}`;
                    window.open(href);
                }
                break;
            default:
            	var file = error.file;
            	var line = error.line;
            	var href = location.href;
                href = href.match(/(.+\/(index.php)?\?).+/)[1];
                var index = file.indexOf('.');
                var key = file.slice(0, index);
                var value = file.slice(index + 1);
                href += `${key}=${value}#${error.line}`;
                window.open(href);
            }
        },
    },
    
    directives: {
        finish :{
            mounted(el, binding){
            },
        },
    },
};

//http://docs.mathjax.org/en/latest/web/typeset.html#typeset-clear
//http://docs.mathjax.org/en/latest/advanced/typeset.html
//http://docs.mathjax.org/en/latest/web/typeset.html#typeset-async
//http://docs.mathjax.org/en/latest/web/typeset.html#get-math-items
</script>

<style scoped>
.warning {
  color: #B5A642;
}

.error {
  color: red;
}

.error:hover {
  cursor: pointer;
}

[v-cloak] {
  display: none !important;
}

.bottom-right{
  width: auto;
  height: 50px;
  position: relative;
}

.bottom-right p{
  position: absolute;
  bottom: 0;
  right: 0;
}

.pre-wrap {
  white-space: pre-wrap;
}

span.date {
  font-size: 12px;
}

div.lemma + div.lemma {
    /* add spaces between two consecutive tags of div.lemma */
    margin-top: 2em;
}
</style>