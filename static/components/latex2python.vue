<template>
	<div v-if=show tabindex=12 @keydown=keydown>
		<latex2pythonTitle ref=latex2pythonTitle></latex2pythonTitle>	
		<input type=hidden name=id[] :value=id />
		Python:
		<renderPython ref=python :text=python></renderPython><br>
		LaTex:
		<p v-render v-text=`\\[${latex}\\]`></p>
		<input type=hidden name=training[] :value=training>
		<input type=hidden name=latex[] :value=latex>
		<br>
		<br>
	</div>
</template>

<script>
console.log('import latex2python.vue');

import {Command} from "../js/Command.js"
import Listener from "../js/Listener.js"
import latex2pythonTitle from "./latex2pythonTitle.vue"
import renderPython from "./renderPython.vue"

import CounterPart from "../js/CounterPart.js"
import {get_indices, line_offset, set_focus, is_head_char, is_last_char, head_line_offset, last_line_offset, textarea_textContent} from "../js/textarea.js"

Listener.prototype.__defineSetter__("latex", function(latex) {this.set({latex});});
Listener.prototype.__defineSetter__("python", function(python) {this.set({python});});

export default {
	components: {renderPython, latex2pythonTitle},
	
	props : [ 'id', 'latex', 'python', 'training', 'index'],
	
	data(){
		return {
			showContextmenu: false,
			left: 0,
			top: 0,

			ShiftLeft: false,
			
			is_predicted: false,
			
			undoes: [],
			
			that: new CounterPart(this, {python: null, latex: null}),
			
			index_focused: -1,

			feedback: [],
			prompt: [],

			reward: [],
			min_reward: [],
			max_reward: [],
			upper_comparison: [],
			lower_comparison: [],
			
			show: true,
		};
	},
	
	created(){
		this.$parent.latex2python[this.index] = this;
		
		this.is_predicted = this.is_regex;
	},

	computed: {
		inputs() {
			var {id, python, latex} = this;
			return {id, python, latex};
		},
		
		mysql_training() {
			var {training} = this;
			training = training >= 0? training: ~training;
			if (training & 64)
				training &= -65;
			return training;
		},

		api_python() {
			return this.$parent.api_python;	
		},
		
		kwargs() {
			return this.$parent.kwargs.kwargs;	
		},
		
		model() {
			return this.$parent.model;
		},
		
		generate() {
			return this.$parent.generate;
		},
		
		text: {
			get() {
				return this.$parent.data[this.index].text;	
			},
			
			set(text) {
				this.$parent.data[this.index].text = text;
			},
		},
		
		json() {
			var {id, latex, python, training} = this;
			return {id, latex, python, training};
		},
		
		style_input(){
			var length = strlen(this.text);
			length = length / 2 + 1;
			return `width:${length}em;`;
		},
		
		style_textarea_query() {
			var rows = this.text.rows() * 0.8;
			return `padding-bottom: ${rows}px`
		},

		style_textarea_reply() {
			var style = [];
			for (var i of range(this.reply.length)) {
				if (this.reply[i].isString) {
					var rows = this.reply[i].rows() * 1.8;
					style[i] = `padding-bottom: ${rows}px`;
				}
				else {
					style[i] = [];
					for (var j of range(this.reply[i].length)) {
						var rows = this.reply[i][j].rows() * 1.8;
						style[i][j] = `padding-bottom: ${rows}px`;
					}
				}
			}

			return style;
		},

		mysql() {
			return this.$parent.mysql;
		},
		
		is_torch(){
			return this.$parent.is_torch;
		},

		is_python(){
			return this.$parent.is_python;
		},
		
		compare(){
			return this.$parent.compare;
		},
		
		correct(){
			if (this.compare) {
				return this.correct_comparison(this.upper_comparison) && this.correct_comparison(this.lower_comparison);
			}
		},

		is_erroneous() {
			if (this.compare) {
				return !this.correct;
			}
		},

		true_positive() {
			return this.true_positive_comparison(this.upper_comparison) + this.true_positive_comparison(this.lower_comparison);
		},
		
		sum_predicted() {
			return this.sum_predicted_comparison(this.upper_comparison) + this.sum_predicted_comparison(this.lower_comparison);
		},
		
		sum_labelling() {
			var count = 0;
			for (var [i, reply] of enumerate(this.reply)) {
				if (i)
					count += reply.isArray? reply.length: 1;
				
				if (i < this.reply.length - 1)
					count += reply.isArray? reply.length: 1;
			}

			return count;
		},

		second_last() {
			var {reply} = this;
			var index = reply.length - 2;
			if (reply[index].isArray)
				return reply[index].back();
			return reply[index];
		},

		table() {
			return this.$parent.table;
		},
		
		database() {
			return this.$parent.database;
		},
		
		host(){
			return this.$parent.host;
		},
		
		user(){
			return this.$parent.user;
		},

		token() {
			return this.$parent.token;	
		},
	},

	methods: {
		dblclick_p() {
			delete this.$parent.trigger_save;
			delete this.$parent.kwargs.kwargs.repeat;
		},

		upper_class() {
			return this.error_class(this.upper_comparison, ...arguments)? 'upper-false': '';
		},
		
		lower_class() {
			return this.error_class(this.lower_comparison, ...arguments)? 'lower-false': '';
		},
		
		error_class() {
			var [comparison, ...args] = arguments;
			if (args.length == 2) {
				var [i, j] = args;
				if (comparison[i] == null || comparison[i][j] == null || comparison[i][j]) {
					return;
				}
			}
			else {
				var [i] = args;
				if (comparison[i] == null || comparison[i]) {
					return;
				}
			}
			
			return true;
		},
		
		sum_predicted_comparison(comparison) {
			var count = 0;
			for (var comparison of comparison) {
				if (comparison == null)
					continue;

				if (comparison.isArray) {
					for (var comparison of comparison) {
						if (comparison == null)
							continue;

						++count;
					}
				} 
				else {
					++count;
				}
			}

			return count;
		},
		
		true_positive_comparison(comparison) {
			var count = 0;
			for (var comparison of comparison) {
				if (comparison == null)
					continue;
				
				if (comparison.isArray) {
					for (var comparison of comparison) {
						if (comparison == null)
							continue;
						if (comparison)
							++count;
					}
				}
				else if (comparison)
					++count;
			}
			
			return count;
		},
		
		correct_comparison(comparison) {
			for (var comparison of comparison) {
				if (comparison == null)
					continue;

				if (comparison.isArray) {
					for (var comparison of comparison) {
						if (comparison == null)
							continue;
						
						if (!comparison)
							return false;
					}
				}
				else if (!comparison)
					return false;
			}
			
			return true;
		},
		
		focus() {
		},

		change_textarea(event){
			this.command();
		},
		
		change(event){
			this.command(true);
		},
		
		listen(obj){
			return new Listener(this, obj);	
		},
		
		async_build(){
			var self = this;
			setTimeout(()=>{
				self.build();
			}, 128);
		},
		
		build(){
			//console.log(this.syntax);
		},
		
		async_render(){
		},
		
		keydown(event){
			switch (event.key){
			case 'PageDown':
				break;

			case 'PageUp':
				break;

			case 'Shift':
				this.ShiftLeft = event.code == 'ShiftLeft';
				break;
				
			case 'T':
			case 't':
				break;
			}
		},		
		
		keydown_textarea(event) {
			switch (event.key){
			case 'ArrowUp':
				break;
			case 'ArrowDown':
				break;
			case 'Enter':
				break;
			}
		},
		
		contextmenu(event) {
			if (!this.initialize_selectionPoint())
				return;
			
			console.log(event);
			self = event.target;				
			this.left = event.x + self.getScrollLeft();
			this.top = event.y + self.getScrollTop();				
			this.showContextmenu = true;
			event.preventDefault();
		},
		
		command(){
			var [arg] = arguments;
			if (typeof arg == 'function') {
				var func = arg;
				var self = this;
				function push(){
					self.undoes.push(new Command(func, ...arguments));
				}
				
				return push;
			}
			
			this.$parent.command(this, arg);
		},

		async click_generate_text(model, order, focus) {
			var {rlhfTitle} = this.$refs;
			if (model.isString) {
				rlhfTitle.gpt_model = model;
				return rlhfTitle.click_generate_text(null, order, focus);
			}

			for (var index of range(model.length - 1, -1, -1)) {
				if (model[index]) {
					rlhfTitle.gpt_model = model[index];
					await rlhfTitle.click_generate_text(null, index, focus);
				}
			}

			return model.length;
		},

		async compare_answers(model, reverse) {
			model ||= 'ChatGPT-4';
			var {reply} = this;
			if (reply.length < 2) {
				await sleep(5);
				return this.compare_answers(model, reverse);
			}

			var first = reply[reply.length - 2];
			var first = first.replace(/\s*\n{2,}/g, '\n');
			reply[reply.length - 2] = first;

			var second = reply[reply.length - 1];
			var second = second.replace(/\s*\n{2,}/g, '\n');
			reply[reply.length - 1] = second;

			var list = [first, second];
			if (reverse)
				list.reverse();
			
			return await this.compare_two_answers(model, ...list, reverse);
		},

		async compare_two_answers(model, reply1, reply2, reverse) {
			switch (this.lang) {
			case 'en':
				var order = ['first', 'second'];
				if (reverse)
					order.reverse();
				var [first, second] = order;
				
				var text = [
					"Question:",
					this.text,
					"\nAnswer 1:",
					reply1,
					"\nAnswer 2:",
					reply2,
					`\n\nThe dialog above consists of a question and two answers. Insofar as accuracy, relevance, completeness and brevity of the answer is concerned, please tell me briefly which answer is better?`,
				];
				
				var better = '(?:(slightly|presumably) )?(?:more (?:reasonable|correct|accurate|relevant|detailed|comprehensive|complete|specific|informative|practical|concise|direct|succinct|brief)|better)';
				var which = 'the (?:(first)|(second))';
				var answer = '(?:answer|response|reply)';
				var expr = [
					`/${which}'s ${answer} ((is|was)( thought to be)?|(might|can|([cw]|sh)ould) be (consider|deem)ed) ${better}/i`,
					`/${which} (gave|gives|provide[ds]|present(ed|s)) a ${better} ${answer}/i`,
					`/if a ${better} ${answer} (?:must|should) be (?:chosen|selected)(?:among (?:them|the two(?: ${answer})?))?, I(?: (?:shall|will|might))? (?:choose|select)${which}('s ${answer})?/`,
				];
				break;
			case 'cn':
				var order = ['一', '二'];
				if (reverse)
					order.reverse();
				var [first, second] = order;
				
				var text = [
					"问题：",
					this.text,
					"\n答案1：",
					reply1,
					"\n答案2：",
					reply2,
					`\n\n以上对话包含一个问题及两个答案，就作答内容是否答非所问，切中题意，合乎常理，简洁明了等方面考虑，请简要判断哪个答案更好些？`,
				];
				
				var 更好 = '(?:似乎)?更为?(?:合理|准确|合乎常理|正确|相关|切中题意|详细|全面|简明扼要|简[洁单]明了|简要|好些?)';
				var 哪个 = '第(?:(一)|(二))个';
				var 回答 = '(?:[回作]答|答案)';
				var expr = [
					`/${哪个}的${回答}${更好}/`,
					`/${哪个}(给出|提供)了(一个)?${更好}的${回答}/`,
					`/(?:如果|若)(?:一定|非)?要(?:从(?:中|两者中?))?选择?(?:一个)?${更好}的${回答}，我(?:[将会]|将会)?选择${哪个}的${回答}?/`,
				];
				break;
			}
			
			text = text.join("\n");
			var bool, reply; 
			while (true) {
				var {reply, status_code} = await this.generate(text, model, 'answer', this.lang, false);
				if (status_code) {
					console.log("status_code =", status_code);
					console.log("reply =", reply);
					await sleep(20);
					continue;
				}

				var sql_insert = `insert into corpus.feedback values(0, ${this.lang.mysqlStr()}, ${text.mysqlStr()}, ${reply.mysqlStr()}, 0)`;
				query(this.host, this.user, this.token, sql_insert).then(rowcount => {
					console.log(sql_insert);
					console.log('rowcount = ', rowcount);
				}).catch(error => {
					console.log("error occurred when executing:", sql_insert);
				});
				
				if (reply) {
					var m = null;
					for (var e of expr) {
						if (m = reply.match(eval(e)))
							break;
					}

					if (m) {
						bool = m[1] != null;
						var {index: start} = m;
						var end = start + m[0].length;
						var {database, host, user} = this;
						var href = `query.php?user=${user}&from[${database}]=feedback&text=${text.encodeURI()}`;
						if (host && host != 'localhost')
							href += `&host=${host}`;
						var title = text.replace(/"/g, '\\"');
						reply = reply.slice(0, start) + `<a target=_blank href="${href}" title="${title}">` + reply.slice(start, end) + '</a>' + reply.slice(end);
					}
					else {
						bool = null;
					}
					break;
				}
			}
			
			if (reverse && bool != null)
				bool = !bool;
				
			return [bool, text, reply];
		},

		async sort_and_toggle(model) {
			switch (this.lang) {
			case 'en':
				var text = [
					"A teacher asks:",
					this.text,
					"A student answers:",
					this.reply[1],
					"\nThe text above is the dialog between a teacher and a student, in which the teacher is asking a question while the student is answering the question. So far as the precision, relevance, comprehensiveness of the answer is concerned, please make a judgment to decide whether the student's answer is reasonable?",
				];

				break;
			case 'cn':
				var text = [
					"教师提问：",
					this.text,
					"学生作答：",
					this.reply[1],
					"\n以上是教师的提问和学生的作答，就其回答方式是否答非所问，是否切中题意，是否合乎常理等方面考虑，判断一下学生的作答是否合格？",
					"请先区分出以下三类：合格，不完全合格，不合格；必要时再简要解释(100字以内)。",
				];
				break;
			}
			
			text = text.join("\n");
			
			if (model == null)
				model = 'ChatGPT-4';
			
			while (true) {
				var {reply, status_code} = await this.generate(text, model, 'reply', this.lang, false);
				if (status_code) {
					console.log("status_code =", status_code);					
					console.log("reply =", reply);
					await sleep(20);
					continue;
				}

				if (reply) {
					this.prompt.push(text.replace(/学生/g, 'PharmLC'));
					this.feedback.push(reply.replace(/学生/g, 'PharmLC'));
					break;
				}

			}

			if (this.feedback.back().match(/不完全合格|不够全面|不够合格|不合格|切题不准确|未能直接回答|不能算是合格|不算完整|没有回答第二个问题|尚未完全合格|没有充分回答提问|存在问题|没有解答教师的提问|但没有提及|偏离题目|不够完整|不算完全合格|不够准确|没有完全合格|作答内容过于笼统|作答不完全合格|作答不太合格/) 
					|| this.reply[1].match(/\[ai\]/)) {
				var {training} = this;
				if (training < 0)
					training = ~training;
				if (!training) {
					var [bool, prompt, reply] = await this.compare_answers();
				}
			}
		},

		async set_reward(index, reply, report) {
			var {text, lang, reward, min_reward, upper_comparison, max_reward, lower_comparison} = this;
			var score = await json_post(this.api_reward, {lang, text, reply});
			setitem(this.reward, ...index, score);
			
			var [i] = index;
			if (index.isArray) {
				var hit_upper = min_reward[i] == null || score < min_reward[i];
				var hit_lower = max_reward[i] == null || score > max_reward[i];
			}
			else {
				var hit_upper = true;
				var hit_lower = true;
			}
			
			if (hit_upper) {
				min_reward[i] = score;
				if (i + 1 < reward.length) {
					var next_reward = reward[i + 1];
					if (next_reward == null) {
						
					}
					else if (next_reward.isArray) {
						for (var [j, next_reward] of enumerate(next_reward)) {
							this.setitem(upper_comparison, i + 1, j, next_reward < score, report);
						}
					}
					else {
						this.setitem(upper_comparison, i + 1, next_reward < score, report);
					}
				}
			}
			
			if (hit_lower) {
				max_reward[i] = score;
				if (i) {
					var prev_reward = reward[i - 1];
					if (prev_reward == null) {
						
					}
					else if (prev_reward.isArray) {
						for (var [j, prev_reward] of enumerate(prev_reward)) {
							this.setitem(lower_comparison, i - 1, j, prev_reward > score, report);	
						}
					}
					else {
						this.setitem(lower_comparison, i - 1, prev_reward > score, report);
					}
				}
			}

			if (i) {
				var prev_reward = min_reward[i - 1];
				if (prev_reward != null)
					this.setitem(upper_comparison, ...index, score < prev_reward, report);
			}
			
			if (i + 1 < this.reply.length) {
				var next_reward = max_reward[i + 1];
				if (next_reward != null)
					this.setitem(lower_comparison, ...index, score > next_reward, report);
			}
		},
		
		setitem() {
			var args = [...arguments];
			var report = args.pop();
			setitem(...args);
			if (!args.back() && report) {
				if (!this.err) {
					var {report} = this.$parent;
					++report.err;
					this.err = 1;
				}
			}
		},
		
		async init_that(callback){
			if (this.is_predicted){
				var {database, table, id} = this;
				var sql = `select * from ${database}.${table} where id = '${id}'`;
				var [data] = await query(this.host, this.user, this.token, sql);
				data.entity = JSON.parse(data.entity);
				Object.assign(this.that, data);
			}
			else{
				try{
					var data = this.inputs;
					var algorithm = this.compare;
					switch (algorithm) {
					case 'torch':
						delete data.python;
						break;
					case 'python':
						delete data.latex;
						break;
					default:
						if (this.is_python)
							delete data.latex;
						else if (this.is_torch)
							delete data.python;
					}

					if (data.python) {
						var result = await json_post('run.py', data);
						console.log(result.latex);

                  	  console.log("new p tags have been generated!");
                	  setTimeout(() => {
                		  console.log("MathJax.typesetPromise() due to new generation of p tags");
                		  MathJax.typesetPromise();
                	  }, 1000);
					}
					else if (data.latex) {
						var {latex: text} = data;
						text += '\nPython codes yielding the latex above:\n';
						var {text : python} = await json_post('http://192.168.18.100:5001/generate/facebook/opt-350m/latex', {text});
						var result = {python};
						console.log(python);
					}
					Object.assign(this.that, data);
					Object.assign(this.that, result);
				}
				catch(e){
					console.log(e);
					console.log("error in predicting ", this.pn);
				}
			}
			
			if (callback)
				callback();
		},
		
		swap_view() {
			if (this.that.latex){
				//console.log("before swapping:");
				//console.log("this.$parent.data[this.index] =", this.$parent.data[this.index]);
				var self = this.listen(this.$parent.data[this.index]);
				[self.latex, this.listen(this.that).latex] = [this.that.latex, this.latex];
				[self.python, this.listen(this.that).python] = [this.that.python, this.python];
				if (this.training >= 0)
					self.training = ~this.training;
				
				this.listen(this).is_predicted = !this.is_predicted;
				//console.log("after swapping:");
				//console.log("this.$parent.data[this.index] =", this.$parent.data[this.index]);
				
				this.$parent.command(this, true);
				
				this.$nextTick(()=>{
					//console.log(this, this.swap_view);
					this.focus();	
				});
			}
			else{
				this.init_that(this.swap_view);	
			}
		},
	},
	
    async mounted(){
		if (this.is_python || this.is_torch) {
			this.swap_view();
		}
    },
    
	directives: {
		focus: {
		    mounted(el, binding) {
				el.focus();
		    },
		},
		
		render: {
		    mounted(el, binding) {
		    },

		    updated(el, binding) {
		    },
		},
	},		
}

</script>

<style scoped>

.monospace, .monospace-p, .monospace-form {
	font-style: normal;
	font-family: NSimsun, SimSun, "Courier New", Consolas;
	font-size: 1em;
	font-weight: normal;
	white-space: nowrap;
}

.monospace {
	background-color: rgb(199, 237, 204);
	border-style: none;
	margin-left: -0.1em;
}

.monospace-p {
	white-space: nowrap;
}

div.query, div.reply textarea {
	margin-top: 0.6em;
}

.inline-block {
	display: inline-block;
	vertical-align: middle;
}

textarea {
	resize: none;
	overflow: hidden;
	border: none;
}

textarea:focus {
	color: red;
	outline: none;
	caret-color: rgb(127, 0, 85);
}

ul.sublist {
	border: 2px;
	border-top-style: solid;
	margin-top: 0.6em;
}

ul.reply {
	margin-left: -2em;
}

font.margin-left {
	margin-left: -2.5em;
}

sup.lower-false {
	color: yellow;
	position: relative;
}

sup.upper-false {
	color: red;
	position: relative;
}

sup.upper-false:before {
	position: absolute;
	left: -10px;
	top: -2px;

	content: "↑";
	color: yellow;
}

sup.lower-false:before {
	position: absolute;
	left: -10px;
	top: -2px;

	content: "↓";
	color: red;
}

select.source, font.source {
	font-size: 0.4em;
	color: purple;
}

font.align-top {
	vertical-align: top;
}

</style>

