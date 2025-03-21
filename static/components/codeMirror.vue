<template>
    <textarea ref=textarea :name=name placeholder="">{{text}}</textarea>
</template>

<script>
console.log('import codeMirror.vue');
//import CodeMirror from "../codemirror/lib/codemirror.js"

export default {
    data() {
        return {
            editor: null,
        };
    },
    
    props: ['text', 'name', 'style', 'index', 'theme', 'focus', 'lineNumbers', 'styleActiveLine', 'breakpoint'],

    created() {
    	var codeMirror = this.$parent.codeMirror;
    	if (codeMirror)
        	codeMirror[this.index] = this;
    },
    
    computed: {
    	rows() {
    		console.log('rows = ', this.text.length);
    		return this.text.length;
    	},
    	
    	cols() {
    		console.log('cols = ', Math.max(...this.text.map(text => text.length)));
    		return Math.max(...this.text.map(text => text.length));
    	},
    	
    	breakpointArray() {
    		var array = [];
			for (let line = 0; line < this.breakpoint.length; ++line){
				if (this.breakpoint[line]){
					array.push(line);
				}
			}
    		return array;
    	},
    	
    	lastSibling() {
    		return this;	
    	},
    	
    	firstSibling() {
    		return this;	
    	},
    	
        user() {
            return axiom_user();
        },
        
        module() {
            return document.querySelector('title').textContent;
        },
        
        hash() {
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        },
    },
    
	methods: {
		resume() {
			this.$parent.resume();
		},
		
		save() {
			this.$parent.save();
		},
		
		debug() {
			this.$parent.debug();
		},
		
		set_breakpoint(index){
			this.$parent.set_breakpoint(index);
		},

		clear_breakpoint(index){
			this.$parent.clear_breakpoint(index);
		},

		showBreakPoint() {
			if (!this.breakpoint)
				return;
				
			for (let line of this.breakpointArray){
				this.editor.addLineClass(line, "gutter", "breakpoint");
			}
		},		
		
		showExecutionPoint(previousPoint, currentPoint){
    		this.editor.setCursor(currentPoint, 4);
    		this.editor.addLineClass(currentPoint, "class", "executionPoint");
    		
    		if (previousPoint >= 0)
    			this.editor.removeLineClass(previousPoint, "class", "executionPoint");
		},
	},
	
    mounted() {
		var self = this;
		const {open_lemma_sections, regexp_section} = self.$parent;

		function preppend(prefix) {
			var section = open_lemma_sections;
			if (section.length == 1)
				return `${section[0]}.${prefix}`;
			else
				return section.map(section => `'${section}.${prefix}'`).join(', ');
		}

		async function locate_definition(cm, index, module) {
			var section = open_lemma_sections;
			var section = await form_post('php/request/disambiguate.php', {module, section});
			if (!section)
				return null;

			return section + '.' + module;
		}
		
		async function select_mathlib(module) {
			var sql = `
select 
  name 
from 
  mathlib
where 
  name = "${module}"`;
			var list = await form_post(`php/request/execute.php`, {sql});
			return list.length;
		}

		async function F3(cm, refresh) {
		    var cursor = cm.getCursor();
		    var text = cm.getLine(cursor.line);
			var prefix = text.slice(0, cursor.ch) + text.slice(cursor.ch).match(/^[\w']*/)[0];
		    var m = prefix.match(/([\w']+)(?:\.[\w']+)*$/);
		    var module = m[0];
			m = module.match(/^Axiom\.(.+)/);
			if (m)
				module = m[1];

			var symbol = null;
			var user = axiom_user();
			var table = 'module';
			if (module.indexOf('.') < 0) {
				if (!module.fullmatch(regexp_section)) {
					var symbol = module;
					module = await locate_definition(cm, cursor.line, symbol);
					if (module == null){
						var href = `/${user}?mathlib=${symbol}`;
						if (refresh)
							location.href = href;
						else
							window.open(href);
						return;
					}
					m = text.slice(prefix.length).match(/\.(\w+)/);
					symbol = m? m[1]: null;
				}
			}
			else {
				m = module.match(/^(\w+)\.(.+)/);
				if (m[1].fullmatch(regexp_section)) {
					if (!await form_post('php/request/disambiguate.php', {module: m[2], section : [m[1]]})) {
						if (await select_mathlib(module))
							table = 'mathlib';
						else
							return;
					}
				}
				else{
					var section = open_lemma_sections;
					switch (section.length) {
					case 0:
						if (await select_mathlib(module))
							table = 'mathlib';
						else
							return;
						break;
					case 1:
						if (await select_mathlib(module))
							table = 'mathlib';
						else {
							var [section] = section;
							module = section + '.' + module;
						}
						break;
					default:
						var section = await form_post('php/request/disambiguate.php', {module, section});
						if (section) {
							module = section + '.' + module;
							m = text.slice(prefix.length).match(/\.(\w+)/);
							symbol = m? m[1]: null;
						}
						else if (await select_mathlib(module))
							table = 'mathlib';
						else
							return;
						break;
					}
				}
			}

			var href = user? `/${user}/?${table}=${module}`: location.href.replace(self.module.replace(/\./g, '/'), module.replace(/\./g, '/')).replace(/#\w+$/, '');

			if (symbol)
				href += `#${symbol}`;
			if (refresh)
				location.href = href;
			else
				window.open(href);
		}
		
		function open(cm, ch) {
			var [first, second] = ch.split('');
			cm.replaceSelection(first);

			var cursor = cm.getCursor();
			console.log("cursor.ch = " + cursor.ch);

			var text = cm.getLine(cursor.line);

			var selectionStart = cursor.ch;
			console.log("selectionStart = " + selectionStart);

			var left_parenthesis_count = 0;
			var left_bracket_count = 0;
			var left_brace_count = 0;
			if (text[selectionStart] != '.') {
				for (; selectionStart < text.length; ++selectionStart) {
					var char = text[selectionStart];

					if (char >= 'a' && char <= 'z' || char >= 'A' && char <= 'Z') {
						continue;
					}

					switch (char) {
						case '_':
						case '.':
							continue;
						case '(':
							++left_parenthesis_count;
							continue;
						case '[':
							++left_bracket_count;
							continue;
						case '{':
							++left_brace_count;
							continue;

						case ')':
							if (left_parenthesis_count) {
								--left_parenthesis_count;
								continue;
							}
							else
								break;
						case ']':
							if (left_bracket_count) {
								--left_bracket_count;
								continue;
							}
							else
								break;
						case '}':
							if (left_brace_count) {
								--left_brace_count;
								continue;
							}
							else
								break;
						default:
							if (left_parenthesis_count || left_bracket_count || left_brace_count)
								continue;
					}
					break;
				}
			}

			cm.setCursor(cursor.line, selectionStart);
			cm.replaceSelection(second);
			cm.setCursor(cursor.line, selectionStart);
		}

		function close(cm, ch) {
			var cursor = cm.getCursor();
			if (cursor.ch < cm.getLine(cursor.line).length && cm.getTokenAt({ ch: cursor.ch + 1, line: cursor.line }).string == ch)
				cm.setCursor(cursor.line, cursor.ch + 1);
			else
				cm.replaceSelection(ch);
		}

		var extraKeys = {
			Tab(cm) {
				cm.replaceSelection(' '.repeat(cm.getOption('indentUnit')));
			},

			'Alt-Left': function(cm) {
				history.go(-1);
			},

			'Alt-Right': function(cm) {
				history.go(1);
			},

			Alt(cm) {
			},

			"[": function(cm) {
				open(cm, '[]');
			},

			"]": function(cm) {
				close(cm, ']');
			},

			"Shift-9": function(cm) {
				open(cm, '()');
			},

			"Shift-0": function(cm) {
				close(cm, ')');
			},

			"Shift-[": function(cm) {
				open(cm, '{}');
			},

			"Shift-]": function(cm) {
				close(cm, '}');
			},

			"Alt-/": function(cm) {
				return cm.showHint();
			},

			"Ctrl-/": function(cm) {
				return cm.toggleComment();
			},

			"Ctrl-I": function(cm) {
				var cursor = cm.getCursor();
    			var currentLine = cursor.line;
    			// Start from the beginning of the document
    			var from = { line: 0, ch: 0 };
    			// End at the last character of the current line
    			var to = { line: currentLine, ch: cm.getLine(currentLine).length };
    			// Get all text in this range
    			var text = cm.getRange(from, to);
				console.log('text = ' + text);
				self.code_generation(text);
			},

			".": function(cm) {
				cm.replaceSelection('.');
				return cm.showHint();
			},

            'Ctrl-O': function(cm) {
                console.log("'Ctrl-O' is pressed! self.module = ", self.module);
                var module = self.module;
                if (module.match(/\W$/))
                	module = module.slice(0, -1);
                
                var href = `/${self.user}/?new=${module}`;
                window.open(href);
            },

            'Ctrl-S': function(cm) {
            	form.submit();
            },

			'F5': function(cm) {
            },

            'Shift-Alt-W': function(cm) {
                console.log('Shift-Alt-W');
                var search = location.search;
				var m = search.match(/\?mathlib=(.*)/)
				if (m) {
					var mathlib = m[1];
					search = `?q=${mathlib}&fullText=on`;
					index = search.length;
				}
				else {
					var index = search.lastIndexOf('.') + 1;
                	if (!index)
						index = search.lastIndexOf('/') + 1;
				}
                location.hash = search.substring(index);
                location.search = search.substring(0, index);
            },
            
            'Alt-D': function(cm) {
				const {Pos, deleteNearSelection, clipPos} = CodeMirror;
				deleteNearSelection(cm, range => ({
    				from: Pos(range.from().line, 0),
    				to: clipPos(cm.doc, Pos(cm.lineCount() + 1, 0))
  				}));
				var parent = self.$parent.$parent;
				var {index} = self;
				var i = index.back();
				if (i.isInteger) {
					var list = getitem(parent.renderLean, ...index.slice(0, -1));
					var pre_indices = index.slice(0, -1);
					for (let t = list.length - 1; t > i; --t) {
						parent.delete([...pre_indices, t]);
					}
					list.length = i;
				}
            },

            Left(cm) {
                cm.moveH(-1, "char");
                if (cm.getCursor().hitSide) {
                    if (i == 0) {
                        cm = self.$parent.$refs.apply;
						cm = cm.editor;
                    }
					else {
						cm = extraKeys.Up(cm);
					}
                    
                    cm.focus();
                    CodeMirror.commands.goDocEnd(cm);
                }
            },

            Right(cm) {
                cm.moveH(1, "char");
				if (cm.getCursor().hitSide) {
					cm = extraKeys.Down(cm);
					cm.focus();
					CodeMirror.commands.goDocStart(cm);
				}
            },

            Down(cm) {
                var cursor = cm.getCursor();
                if (cursor.line + 1 < cm.lineCount())
                    return cm.moveV(1, "line");

                cm = self.nextSibling.editor;
                cm.focus();
                if (cursor.ch == 0) {
                    var linesToMove = cm.getCursor().line;
                    for (let i = 0; i < linesToMove; ++i)
                        cm.moveV(-1, "line");
                }
                else
                    cm.setCursor(0, cursor.ch);
            },

            Up(cm) {
                var cursor = cm.getCursor();
                if (cursor.line > 0)
                    return cm.moveV(-1, "line");
                cm = self.previousSibling.editor;
				cm.focus();
				if (cursor.ch == 0) {
					var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
					for (let i = 0; i < linesToMove; ++i)
						cm.moveV(1, "line");
				} 
				else if (cm.lineCount)
					cm.setCursor(cm.lineCount() - 1, cursor.ch);
				else
					cm.selectionStart = cm.selectionEnd = cursor.ch;
            },

            "Ctrl-Enter": cm => {
                CodeMirror.commands.newlineAndIndent(cm);
            },
            
            PageUp(cm) {
                var cursor = cm.getCursor();
                if (cursor.line >= 18)
                    return cm.moveV(-1, "page");
                
                cm = self.previousSibling.editor;
                cm.focus();
                if (cursor.ch == 0 || i == 0) {
                    var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
                    for (let i = 0; i < linesToMove; ++i)
                        cm.moveV(1, "line");
                }
                else
                    cm.setCursor(cm.lineCount() - 1, cursor.ch);
            },

            PageDown(cm) {
                var cursor = cm.getCursor();
                if (cursor.line + 18 < cm.lineCount())
                    return cm.moveV(1, "page");

                var cm = self.nextSibling.editor;
                cm.focus();

                if (cursor.ch == 0) {
                    var linesToMove = cm.getCursor().line;
                    for (let i = 0; i < linesToMove; ++i) {
                        cm.moveV(-1, "line");
                    }
                }
                else
                    cm.setCursor(0, cursor.ch);
            },
            
            F3(cm){
            	F3(cm, false);
            },

            'Ctrl-F3': cm => F3(cm, true),

            'Ctrl-End': cm => {
                cm = self.lastSibling.editor;
                cm.focus();
                return cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
            },

            'Ctrl-Home': cm => {
                cm = self.firstSibling.editor;
                cm.focus();
                return cm.extendSelection(CodeMirror.Pos(cm.firstLine(), 0));
            },       
            
			'Shift-Ctrl-B': function(cm) {
				var line = cm.getCursor().line;
				console.log('line = ', line);
				if (self.breakpoint[line]){
					cm.removeLineClass(line, "gutter", "breakpoint");
					self.clear_breakpoint(line);
				}
				else{					
					cm.addLineClass(line, "gutter", "breakpoint");
					self.set_breakpoint(line);
				}
			},

			F8(cm) {
				self.resume();
			},

			Delete(cm) {
				cm.deleteH(1, "char");
			},
        };
        
        if (typeof CodeMirror == 'undefined')
        	return;
        
        this.editor = CodeMirror.fromTextArea(this.$el, {
            mode: {
                name: "lean",
                singleLineStringErrors: false
            },
            
            theme: this.theme,

            indentUnit: 2,

            matchBrackets: true,

            scrollbarStyle: null,

            extraKeys,
            
            lineNumbers: this.lineNumbers,
            
            styleActiveLine: this.styleActiveLine,

            hintOptions: { 
                hint(cm, options){
                	var Pos = CodeMirror.Pos;
                	return new Promise(function(accept) {
                		var cur = cm.getCursor();
                		var token = cm.getTokenAt(cur);
                		var tokenString = token.string;
                		console.log('tokenString = ' + tokenString);

						var line = cm.getLine(cur.line);
						var text = line.slice(0, cur.ch);
						var prefix = text.match(/\\[\w.|<>=^~{} \\+-]+$|[\w.]+$/)[0];

						var user = axiom_user();

						var m;
						var search_lemma = tokenString == '.' && prefix[0] != '\\' || prefix[0] =='.';
						if (search_lemma || (prefix.indexOf('.') >= 0 && prefix[0] != '\\')) {
							if (search_lemma) {
								token.start += 1;
								m = !prefix.match(new RegExp(`^(${regexp_section.source})`, 'g'));
							}
							else {
								m = prefix.match(/([\w.]*\.)(\w*)$/);
								var [_, prefix, phrase] = m;
								m = prefix.match(/^(\w*)\.$/);
								m = m && !m[1].fullmatch(regexp_section);
									
							}
							if (m)
								prefix = preppend(prefix);
							if (prefix.isArray) {
								var sql = `
select 
  distinct substring_index(substring(module from length(jt.prefix) + 1), '.', 1) as phrase
from 
  lemma 
  join 
    json_table(
      '${JSON.stringify(prefix)}', 
      '$[*]' columns(prefix varchar (${Math.max(...prefix.map(word => word.length))}) path '$')
    ) as jt
where 
  user = '${user}' and module like concat(jt.prefix, '%')`;
							}
							else {
								var sql = `
select distinct substring_index(substring(module from length('${prefix}') + 1), '.', 1) as phrase
from 
  lemma 
where 
	user = '${user}' and module like concat('${prefix}', '%')`;
							}

							if (!search_lemma)
								sql += ` having phrase regexp '${phrase}' COLLATE utf8mb4_0900_bin`;
						}
						else {
							token.start -= prefix.length - tokenString.length;
							var match_unicodedata_right_open = prefix.fullmatch(/\\N\{[A-Z\d -]+/i) && line[cur.ch] == '}';
							if (match_unicodedata_right_open || prefix.fullmatch(/\\N\{[A-Z\d -]+\}/i)) {
								if (match_unicodedata_right_open) {
									token.end += 1;
									var hint = prefix.slice(3);
									var sql = `
with _t as (
	select unicode, name from unicode where name like '%${hint}%'
)
SELECT
  CASE
    WHEN name = '${hint}' or (SELECT COUNT(*) FROM _t) = 1
      THEN unicode
    ELSE
      concat('\\\\N{', name, '}')
  END
FROM
  _t`;
								}
								else {
									var hint = prefix.slice(3, -1);
									var sql = `
SELECT
  unicode
FROM
  unicode
where name = '${hint}'`;
								}
							}
							else if (m = prefix.match(/^\\(.+)/)){
									var hint = m[1];
									var sql = `
with _t as (
  select 
    unicode, jt.latex
  from 
    unicode 
  cross join json_table(
    latex,
    '$[*]' COLUMNS (latex varchar(255) PATH '$')
  ) as jt
  where 
    jt.latex like binary'${hint}%'
)
select 
  CASE
    WHEN (SELECT COUNT(*) FROM _t) > 1 THEN 
      _t.latex
    ELSE 
      unicode
  END as unicode
from 
  _t
union
select 
  unicode
from 
  _t
where 
  latex = '${hint}'
order by char_length(unicode)`;
							}
						}

						sql += "\nlimit 20";
						console.log(sql);
                		form_post(`/${user}/php/request/execute.php`, {sql}).then(list => {
                			// Find the token at the cursor
							list = list.map(item => item[0]);
                			console.log('hint = ' + list);
                			return accept({
                				list,
                				from: Pos(cur.line, token.start),
                				to: Pos(cur.line, token.end)
                			});
                		});
                	});
                },  
            },
        });

        //this.editor.setSize('auto', 'auto');
        
        if (this.focus)
        	this.editor.focus();
        
		// Get the editor's wrapper element
		const wrapper = this.editor.getWrapperElement();

		// Add a capture-phase mousedown listener to intercept events early
		wrapper.addEventListener('mousedown', function(e) {
			console.log('Mouse down event:', e);
			if (e.button === 0) { // Left mouse button
				console.log('Left mouse button clicked in codeMirror.vue');
				self.$parent.click_left(e);
			}
		}, { capture: true });

        if (this.hash){
        	var line = null, col = 4;
        	if (typeof this.hash == 'number') {
        		line = this.hash;
            }
        	else {
        		var m = this.hash.match(/^(\d+)(?::(\d+))?/);
        		if (m){
        			var line = m[1];
        			line = parseInt(line) - 1;
        			if (m[2] != null)
        				col = parseInt(m[2]) - 1;
        		}
            }
            
        	if (line != null)
				return this.editor.setCursor(line, col);
			
            var regex = eval(`/((?:    )*def ${this.hash})\\([^()]+\\):\\s*$/`);

            var size = this.editor.lineCount();
            for (var index = 0; index < size; ++index) {
                var line = this.editor.getLine(index);
                //console.log(line);

                var m = line.match(regex);
                if (m) {
                	this.editor.setCursor(index, m[1].length - this.hash.length / 2);
                    break;
                }
            }    	
        }
    },
}
</script>

<style>
.CodeMirror {
    /*overflow-y: visible; */
    height: auto !important;
    width: auto !important;
}

.CodeMirror-scroll {
	/* Set scrolling behaviour here */
	overflow: auto;
	max-height: 2000px;
}

.CodeMirror-focused .CodeMirror-selected {
	background: rgb(0, 120, 215);
}

.breakpoint:before{
	width: 4px;
	height: 1.5px;
	position: absolute;
	left: 0px;
	top: 11.5px;
	content: "";
	transform: rotate(-45deg);
	background: #00FF00;
	box-shadow: 1px 1px 0 0 #9da0a0;
	z-index: 0;
}
    
.breakpoint:after {
	width: 6px;
	height: 6px;
	position: absolute;
	left: 2.3px;
	top: 6px;
	content: "";
	background: #00FF00;
	border-radius: 50%;
	box-shadow: 1px 1px 0 0 #9da0a0;
	z-index: 0;
}

.executionPoint > pre > span {
	background-color: #5a5;
}

</style>