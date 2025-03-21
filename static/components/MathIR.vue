<template>
	<div tabindex=2 @keydown=keydown_s>
		<mysql :host=host :user=user :token=token :sql=sql :kwargs=kwargs :rowcount=data.length ref=mysql></mysql>
		<form tabindex=1 name=form :action=action method=post class=monospace-form>
			<div>
				<latex2python v-for="(data, index) of data" :id=data.id :latex=data.latex :python=data.python :training=data.training :index=index></latex2python>
			</div>
			<input type=hidden name=table :value=table>
		</form>
		
		<div v-if=report.sum v-focus tabindex=4>
			<div style=float:right>
				number of testing cases: {{data.length}}<br>
				there {{report.err <= 1? 'is' : 'are'}} {{report.err}} {{report.err <= 1? 'error' : 'errors'}} in all, <button class=transparent @click=click_simplify>{{report.simplify? 'show all tables': 'show errors only'}}</button>
				{{report.simplify? 'to inspect in detail.': 'to simplify the report.'}}<br>
				remaining: {{data.length - report.sum}} to be evaluated...<br>
				remaining list:<br>
				<template v-if="data.length - report.sum < 10" v-for="id of remainingList">id = {{id}}<br></template>
			</div>
			<table class=report border=1>
				<tr>
					<th colspan=2>testing synopsis</th>
				</tr>
				<tr>
					<th>\</th><th>accuracy</th>
				</tr>
				<tr>
					<td align=middle><font color=green>reward</font></td>					
					<fraction :numerator="report.sum - report.err" :denominator=report.sum :operator="'='"></fraction>
				</tr>
			</table>
		</div>
		<timer v-if=trigger :cond="data.length - report.sum" :trigger=trigger style=float:right></timer>
		
		<template v-if="data.length == 1">
			<button class=navigate @click=click_next>
				Keyboard PageDown (=>Next)
			</button> or 
			<button class=navigate @click=click_previous>
				Keyboard PageUp (Previous<=)
			</button>
		</template>
		<div v-else-if=data.length>
			<button type=button class=transparent @click=click_download>download</button>
			<input type=text :value="download_option.limit || data.length" size=4 @input="download_option.limit = $event.target.value" /> 
			<select v-model=download_option.type>
				<option v-for="value of ['text', 'json', 'html']" :value=value>{{value}}</option>
			</select> 
			results  
			<select v-model=download_option.source @change=change_select>
				<option v-for="value of ['labelled', 'predicted']" :value=value>{{value}}</option>
			</select>, 
			with offset = <input type=text v-model=download_option.offset size=4 /><br>
		</div>
	</div>
</template>

<script>
console.log('import MathIR.vue');

import mysql from "./mysql.vue"
import latex2python from "./latex2python.vue"
import Undoer from "../js/Undoer.js"
import {Command, command} from "../js/Command.js"
import {props, piece_together} from "../js/mysql.js"
import TreeNode from "../js/TreeNode.js"
import fraction from "./fraction.vue"
import timer from "./timer.vue"
import {construct_rich_text} from "../js/RichText.js"

export default {
    components: {mysql, latex2python, fraction, timer},

	props,
	
    data() {
        return {
        	latex2python: [],
        	
        	indexFocused: -1,
        	
			undoer: new Undoer(),
			
			download_option: {
				source: 'labelled',
				type: 'json',
			},
			
			mounted: {},

        	report: {
           		sum: 0,
           		err: 0,
        	},
        };
    },
    
    computed: {
    	trigger() {
    		return this.is_torch? this.trigger_simplify: this.repeat? this.trigger_save: null;	
    	},
    	
    	api_python() {
   			return 'run.py';
    	},
    	
    	repeat() {
    		var {kwargs} = this;
    		return kwargs.kwargs && kwargs.kwargs.repeat;
    	},
    	
    	action() {
    		var {action_insert} = this.mysql;
   			return action_insert;
    	},

    	database() {
    		return this.mysql.database;	
    	},
    	
    	mysql() {
    		return this.mounted.mysql? this.$refs.mysql: {};
    	},  
    	
		is_torch() {
    		var {kwargs} = this.kwargs;
			return kwargs && kwargs.torch;
		},
		
		is_python() {
			var {kwargs} = this.kwargs;
			return kwargs && kwargs.python;
		},
		
		is_mysql() {
			return getParameter('mysql') || getParameter('cmd') == 'select' || this.cmd == 'update';
		},

		compare() {
			if (this.is_torch)
				return 'torch';
		},

		model() {
			var {kwargs} = this.kwargs;
			if (!kwargs)
				return;
			
			var {model} = kwargs;
			if (!model)
				return;
			
			if (model.isArray)
				return model;
			
			if (model.isString)
				return model;

			var array = [];
			for (var [index, model] of Object.entries(model)) {
				array[index] = model;
			}

			return array;
		},
    },
    
    created() {
    	this.report.simplify = this.getSimplify();
    },
    
    methods: {
    	command,
    	
    	getSimplify() {
    		var simplify = getParameter('kwargs[simplify]');
    		return simplify && simplify.toLowerCase() == 'true';
    	},
    	
		async click_next(event) {
    		if (this.model) {
    			this.forward_next();
    		}
    		else
				this.navigate(1);
		},
		
		async click_previous(event) {
			this.navigate(-1);
		},
		
		async navigate(delta) {
			var {id, training} = this.data.back();
			var kwargs = {};
			var back = this.latex2python.back();
			this.mysql.navigate(
					delta, 
					id, 
					training, 
					back.lang, 
					kwargs);
		},
    	
		click_download(event) {
			var {type, usefulness, limit, offset, file, source} = this.download_option;
			
			var data = this.latex2python.map(self => {
				switch (type){
				case 'json':
					return self.json;
				}
    		});
			
			if (offset){
				offset = parseInt(offset);
				if (offset < 0)
					offset += data.length;
				data = data.slice(offset);
			}
			
			if (limit){
				limit = parseInt(limit);
				data = data.slice(0, limit);
			}
			
			data = JSON.stringify(data, null, 4);
			var blob = new Blob(
					[data],
					{
						type: "text/plain;charset=utf-8",
						endings: 'native'
					});
			
			if (file){
				var [name, ext] = split_filename(file);
				file = `${name}.json`;
			}
			else{
				file = `${source}.json`;
			}
			
			saveAs(blob, file);
		},
		
    	keydown_s(event){
			var self = event.target;
			var key = event.key;
			switch (key){
			case 'S':
			case 's':
				if (!event.ctrlKey)
					break;
				
				document.mysql.querySelector('input[type=text]').focus();
				this.$nextTick(()=>{
					form.submit();
				});

				event.preventDefault();
				break;
				
			case 'Z':				
			case 'z':
				if (!event.ctrlKey)
					break;
				
				this.undoer.undo();
				break;
			}    		
    	},
    	
    	async insert(data) {
        	var database = this.database;
        	var table = this.table;
			var training = getParameter("training");
			if (training)
				training = ~training;
			else
				training = ~0;

        	var [{id}] = await query(this.host, this.user, this.token, `select max(id) as id from ${database}.${table}`);
        	var id = parseInt(id);
        	for (var obj of this.data) {
        		if (obj.id > id)
        			id = obj.id;
        	}

			for (var obj of data) {
				if (obj.training == null)
					obj.training = training;
				else if (obj.training >= 0)
					obj.training = ~obj.training;

				var {python, latex} = obj;
				if (python == null)
					obj.python = ''
				
				if (obj.latex == null) {
					var {latex} = await json_post('run.py', {python});
					obj.latex = latex;
				}
				
				if (!obj.id)
					obj.id = ++id;
				
				this.data.push(obj);
			}
    	},
    	
    	process(name, data) {
    		var [pn, ext] = split_filename(name);

            switch (ext.toLowerCase()) {
            case 'json':
            	if (data.isString)
                	data = JSON.parse(data);
                if (!Array.isArray(data)){
                	if (data.training == null) {
                		data.training = 1;
                	}
                	data = [data];
                }
                break;
                
            case 'txt':            	
                data = data.trim().split(/\r*\n+/);
                data = data.map(data => {
                	try {
                		return JSON.parse(data);	
                	}
                	catch (e) {
                		return {};
                	}
                });
                
                break;

            case 'jsonl':
            	data = data.split(/\r?\n/).map(line => {
            		try {
            			return JSON.parse(line);
            		}
            		catch (err) {
            			console.log(err);
            			return {};
            		}
            	});
                break;
            }
            
            this.insert(data);
    	},

    	async click_generate() {
    		if (this.latex2python.length == 1) {
    			this.latex2python[0].click_generate_text('PharmLC-0.1');
    			return;
    		}
    		
    		var queries = [];
    		var lang = [];
   			for (var qa of this.latex2python) {
   				queries.push(qa.text);
   				lang.push(qa.lang);
   			}
   			
   			this.data.clear();   			
   			lang = majority(lang);
   			
   			var count = 0;
   			while (count < queries.length) {
   	   			var query = sample(queries, 10);
   	   			switch (lang) {
   	   			case 'en':
   	   				var text = "Come up with a series of tasks:\n";
   	   				break;
   	   			case 'cn':
   	   				var text = "请帮我续写以下问题列表：（要求生成的问法与列表中问法大致相似，问题的主题与科学技术相关）\n" ;
   	   				break;
   	   			}
   	   			
   	   			for (var [i, q] of enumerate(query)) {
   	   				text += `${i + 1}. ${q}\n`;
   	   			}
   	   			
   	   			i = query.length;
   	   			text += `${i + 1}. `;
   	   			var {reply, status_code} = await this.generate(text, 'ChatGPT-4');

   				if (status_code) {
   					console.log("status_code =", status_code, "abnormal program termination!");
   					break;
   				}
   				
   				var query = reply.split('\n');
   				data = query.map(text => {
   					text = text.trim();
   					var m = text.match(/^\d+\.? *([\s\S]+)$/);
   					if (m)
   						text = m[1];
   					text = text.trim();
   					return {text, reply: [], training: 0, lang};
   				});
   	   			
   				this.insert(data);
   				
   				count += data.length;
   				
   				console.log("count =", count);
   			}
    	},
    	
    	async generate(text, model, type, lang, concise, num_return_sequences) {
    		while (!this.api_openai) {
    			console.log('mysql has not yet finished mounting, waiting for 1 second');
    			await sleep(1);
    		}

    		switch (type) {
    		case 'answer':
    			switch (model) {
    			case 'ChatGPT-3.5':
    			case 'ChatGPT-4':
    			case 'Google-Bard':
        			if (!concise)
        				break;

        			text += "\n";
   					switch (lang) {
       				case 'en':
       					var query_generator = [
       						"Please generate the answer within 100 words.",
       						"Please give me the answer with no more than 100 words.",
       					];
       					break;
       				case 'cn':
       					var query_generator = [
       						"请简要作答，要求在50字以内。",
       						"请在50字以内简要作答。",
       						"请最多使用50字简要作答。",
       					];
       					break;
       				}
   					text += sample(query_generator, 1)[0];    					

    				break;
    			default:
    				break;
        		}
				break;

    		case 'prompt':
    			text += "\n";
				switch (lang) {
				case 'en':
					var query_generator = [
						"Please generate some relevant questions based on the text above.",
						"Could you please come up with some good questions for the passage above?",
						"Please generate some questions about the topic above.",
						"Generate some questions that have answers from the text mentioned above.",
					];
					break;
				case 'cn':
					var query_generator = [
						"请根据以上文本生成一些相关问题。",
						"请根据以上段落提出一些相关问题。",
						"请根据以上话题生成一些相关问法。",
						"请生成一些答案为以上文本的提问。",
					];
					break;
				}
				text += sample(query_generator, 1)[0];
    			break;
    		}
    		
    		console.log("prompt:", text);
    		switch (model) {
			case 'ChatGPT-3.5':
			case 'ChatGPT-4':
			case 'Google-Bard':				
				var api = this.api_openai;
				break;

			case 'PharmLC-0.1':
			case 'PharmLC-0.3':
				var api = this.api_openai;
				//var api = this.api_answer;
				break;
    		}
    		
    		return await json_post(api, {text, model, num_return_sequences});
    	},
    	
    	trigger_save(event) {
    		form.submit();
    	},
    	
    	trigger_simplify() {
    		if (this.report.simplify) {
    			this.report.simplify = false;
    			this.click_simplify();
    		}
    	},
    	
		click_simplify(event) {
			if (this.report.simplify){
				for (var latex2python of this.latex2python){
					latex2python.show = true;
				}
				this.report.simplify = false;
			}
			else{
				for (var latex2python of this.latex2python){
					latex2python.show = latex2python.is_erroneous;
				}
				this.report.simplify = true;
			}
		},
		
		forward_next() {
			var {kwargs, user, host, database, table} = this;
			console.log(kwargs);
			kwargs.select = '*';
			var limit = getParameter('limit');
			if (limit == null)
				limit = 1;

			kwargs.limit = limit;
			kwargs.from = fromEntries(database, table);

			var url = [];
			url.push(`user=${user}`);
			if (host && host != 'localhost')
				url.push(`host=${host}`);

			url.push(...piece_together(kwargs));

			kwargs = {};
			var model = this.model;
			if (model)
				kwargs.model = model;
			if (getParameter('kwargs[repeat]'))
				kwargs.repeat = true;

			if (getParameter('kwargs[reverse]'))
				kwargs.reverse = true;
			
			location.search = get_url({kwargs}) + '&' + url.join('&');
		},
    },

    mounted() {
    },
    
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	el.focus();
		    },
		},
	},		
    
}
</script>

<style>
</style>
