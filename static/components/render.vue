<template>
    <div v-finish>
        <form name=form spellcheck=false enctype="multipart/form-data" method=post action="">
            <font color=blue>theorem </font> {{ namespace.theorem.name}}
            <renderProve :text=given :index=0></renderProve>
            <template v-if=latex.given>
                <hr>
                <a style='font-size: inherit' :href="`/${user}/?callee=${module}`" title='callee hierarchy'>
                    <font color=green><b>-- given</b></font>
                </a>
                <p>{{latex.given}}</p>
            </template>
            <hr>
            <a style='font-size: inherit' :href="`/${user}/?callee=${module}`" title='callee hierarchy'>
                <font color=green><b>-- imply</b></font>
            </a>
            <p>{{latex.imply}}</p>

            <hr>
            <a style='font-size: inherit' :href="`/${user}/?caller=${module}`" title='caller hierarchy'>
                <font color=green><b>-- proof</b></font>
            </a>

            <template v-for="(lean, index) in proof">
                <renderProve :text=lean :index="index + 1"></renderProve>
                <p>{{latex.proof[index]}}</p>
            </template>

        </form>

        <template v-if="error.length != 0">
            <br><br>
            <h3>error information is printed as follows:</h3>
        </template>

        <font v-for="(err, index) of error" class=error :title=err.file @click="click_font(index, err.line)">
            <template v-if=!index>
            	{{err.type}}: {{err.info}}<br>
            </template>
            {{err.code}}<br>
        </font>

        <div class=bottom-right>
            <p>
                <a :href="href_remote" target="_blank"><font size=2>Created on {{date.created}}</font></a>
                <br>
                <font v-if=updatedTime size=2>Updated on {{date.updated}}</font>
            </p>
        </div>
        
    </div>
</template>

<script>
console.log('import render.vue');
import renderProve from "./renderProve.vue"
import renderApply from "./renderApply.vue"

export default {
    components: {renderProve, renderApply},
    props : [ 'imports', 'open', 'namespace', 'error', 'module', 'date', 'latex'],
    
    async created(){
    },
    
    data(){
        return {
        	renderProve: [],
        };        
    },
    
    computed: {
        given() {
            var {typeclass, kwargs, given} = this.namespace.theorem;
            var args = [];
            if (typeclass)
                args.push(typeclass);
            if (kwargs)
                args.push(kwargs);
            if (given)
                args.push(given);
            return args.join('\n') + ' :';
        },

        imply() {
            return this.namespace.theorem.imply;
        },

        proof() {
            var {proof} = this.namespace.theorem;
            return proof.by?? proof;
        },

        user(){
            return axiom_user();
        },

        numOfRequisites(){
            var m = this.module.match(/([\w.]+)\.(to|of)\./);
            if (m.length){
                return m[1].split('.').length - 1;
            }
            return 0;
        },
        
        hash(){
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        },

        href_remote(){
            var hostname = location.hostname == 'localhost'? '192.168.18.132': 'localhost';
			var port = location.hostname == 'localhost'? '8000': '80';
			var {pathname, search, hash, protocol} = location;
			return `${protocol}\/\/${hostname}:${port}${pathname}${search}${hash}`;
        },
    },

    updated(){
    },
    
    mounted(){
    },
    
    methods: {
        click_font(index, line) {
        	console.log(`index = ${index}, line = ${line}`);
        	var error = this.error[index];
        	switch(error.func){
        	case 'prove':
                var line = this.error.line;
                var sum = 0;
                
                console.log("this.renderProve.length = " + this.renderProve.length);
                for (let cm of this.renderProve) {
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
                var self = binding.instance;
                
                console.log('module = ' + self.module);

                for (var theorem of binding.instance.imports) {
                    var m = theorem.fullmatch(/Axiom\.([\w.]+)/);
                    if (!m)
                        continue;
                    theorem = m[1];
                    console.log('theorem = ' + theorem);
                    for (let cm of self.renderProve) {
                        cm = cm.editor;
                        cm.eachLine(line => {
                            var text = line.text;
                            var selectionStart = text.indexOf(theorem);
                            if (selectionStart >= 0) {
                                console.log(text);
                                var lineNo = line.lineNo();

                                cm.setCursor(lineNo, selectionStart);
                                cm.addSelection({ line: lineNo, ch: selectionStart }, { line: lineNo, ch: selectionStart + theorem.length });
                                cm.focus();
                            }
                        });
                    }
                }
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

</style>