<template>
	<div tabindex=2 @keydown=keydown>
		
		<div v-if=edit>
			<textarea v-focus :rows=rows :cols=cols @input=input_textarea>{{sql}}</textarea>
		</div>
		<div v-else>
			<span class=hover>
				{{hint}}
			</span>
			<p v-click :class=cmd @dblclick=dblclick data-clipboard-action=copy :style=style_p :data-clipboard-target=`p.${cmd}` @mouseover=mouseover_p @mouseout=mouseout_p>
				{{sql.isArray? sql.join(';\n'): sql}}
			</p>
		</div>
		<template v-if=rowcount.length>
			rowcount = {{rowcount.back()}}<template v-if="rowcount.length > 1">, cumulative rowcount = {{rowcount.sum()}}</template>
		</template>
		<template v-else>
			{{mysql_result_hint}}
		</template>
	</div>
</template>

<script>

console.log('import mysqlExecute.vue');

export default {
	props : ['cmd', 'sql', 'next'],
	
    data() {
		return {
			hint: 'click to copy the text, double click to execute the mysql statement',
			edit: false,
			rows: 0, 
			cols: 0,

			wait: false,

			rowcount: [],
			errors: 0,
		};
    },
    
    created() {
    	//var {cmd, sql} = this;
    	//console.log({cmd, sql});
    },

    computed: {
		cmds() {
			return this.$parent.cmds;
		},

		host() {
			return this.$parent.host;
		},
		
		user() {
			return this.$parent.user;
		},
		
		token() {
			return this.$parent.token;
		},
    	
    	mysql_result_hint() {
    		var {rowcount} = this.$parent;
    		if (rowcount == null)
    			return 'Empty Set';
    		
    		var hint;
    		switch (rowcount) {
    		case 0:
    			hint = 'Empty ';
    			break;
    		case 1:
    			hint = '1 row in ';
    			break;
    		default:
    			hint = `${rowcount} rows in `;
    			break;
    		}
    		
    		return hint + 'set';
    	},
    	
    	execute() {
    		return this.$parent.execute;	
    	},
    	
    	repeat() {
    		return this.$parent.repeat;	
    	},
    	
    	rowsOfSQL() {
    		var {sql} = this;
    		if (sql.isArray)
    			return sql.length;

			return sql.split(/\n/).length;
    	},

    	style_p() {
    		var css = [];
    		if (this.rowsOfSQL > 12)
    			css.push("overflow-y: scroll");
    		
    		if (this.rowsOfSQL > 1) {
    			css.push("white-space: pre");
        		var height = 20 * this.rowsOfSQL.clip(6, 12);
        		css.push(`height: ${height}px`);
    		}
    		
    		if (this.wait) 
    			css.push(`cursor: wait`);
    		
    		return css.join("; ");
    	},

    	query() {
    		var {host} = this;
    		if (host && (this.$parent.from || this.$parent.from == 0))
       			host = null;
   			return sql => query(host, this.user, this.token, sql);
    	},
    },

	mounted(){
		create_ClipboardJS('p.' + this.cmd);	
	},
    
	methods: {
		async dblclick(event){
			var self = event.target;
			var {sql} = this;
			
			console.log(sql + ';');
			if (Array.isArray(sql)){
				this.hint = 'click to copy the text';
				this.wait = true;
				var rowcount = await this.query(sql);
				console.log("rowcount = ", rowcount);
				this.rowcount.push(...rowcount);
				this.wait = false;
				rowcount = rowcount.sum();
				if (rowcount && this.repeat) {
					this.dblclick(event);
				}
				else {
					sql.clear();
					if (this.next)
						this.next();
				}
			}
			else{
				sql = sql.trim();
				if (sql.startsWith('replace'))
					return;
				
				if (sql.match(/^(select|with|show|with) /)){
					this.wait = true;
					var result = await this.query(sql.replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">"));
					this.wait = false;

					var hover = self.parentElement.querySelector('.hover');
					var match = /^select \* from (\w+(\.\w+)?)/.exec(sql);
					if (match) {
						var tableName = match[1];
						sql = "replace into %s (%s) values ";
						if (result.length){
							var array = [];
							for (let dict of result) {
								console.log(dict);
								var values = [];
								for (let value of Object.values(dict)){
									var string = JSON.stringify(value);
									//string.match(/\\u[\da-f]+/)
									if (string.match(/\\u/)) {
										string = [...value].map(ch => {
											var hex = ord(ch).toString(16);
											if (hex.length & 1)
												hex = '0' + hex;
											return hex;
										});
										
										var maxLength = Math.max(...string.map(ch => ch.length));
										if (maxLength == 2) {
											string = string.join('');
											string = `x'${string}'`;
										}
										else {
											string = string.map(ch => ch.length == 4? ch: '00' + ch).join('');
											string = `_ucs2 0x${string}`;
										}
									}
									
									values.push(string);
								}
								array.push("(%s)".format(values.join(', ')));
							}

							sql = sql.format(tableName, Object.keys(result[0]).join(', '));
							
							this.hint = 'click to copy the text or press Insert to edit the content';
							setAttribute(this, 'sql', sql + array.join(', '));
						}
						else{
							setAttribute(this, 'sql', '[]');
						}
					}
					else {
						var rowcount = result;
						if (rowcount && this.repeat) {
							this.rowcount.push(rowcount);
							this.hint = `execution of sql statement has succeeded, rowcount = ${rowcount}`;
							if (this.rowcount.length > 1) {
								this.hint += `, cumulative rowcount = ${this.rowcount.sum()}`;
							}
							this.dblclick(event);
						}
						else
							setAttribute(this, 'sql', JSON.stringify(result));
					}
				}
				else{
					sql = sql.replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">");
					var {database, table} = this.$parent;
					var sqls = sql.split(eval(`/;\\n(?=update ${database}.${table} set \\w+ = .*)/`));
					if (sqls.length > 1)
						sql = sqls;

					this.wait = true;
					try {
						var yields = await this.query(sql);	
					}
					catch (err) {
						var yields = err;
					}

					if (yields && yields.isArray) {
						var rowcount = yields.sum();
					}
					else {
						var rowcount = parseInt(yields);	
					}

					if (rowcount.isNaN) {
						++this.errors;
						
						var sleepPeriod = this.errors < 6? `${this.errors * 10} seconds`: `${this.errors / 6} minutes`; 
						this.hint = `execution of sql has failed, sleeping for ${sleepPeriod}`;
						if (this.rowcount.length) {
							this.hint += `, previous rowcount = ${this.rowcount.back()}`;
							if (this.rowcount.length > 1)
								this.hint += `, cumulative rowcount = ${this.rowcount.sum()}`;
						}
						
						console.log(yields);
                        if (this.repeat || confirm("error occurred during processing, retry?")) {
							setTimeout(()=>{
								this.dblclick(event);
							}, this.errors * 10000);
                            return;
                        }
					}
					else {
						if (this.errors) {
							this.errors >>= 1;
						}
						
						this.rowcount.push(rowcount);
						this.hint = `execution of sql statement has succeeded, rowcount = ${rowcount}`;
						if (this.rowcount.length > 1) {
							this.hint += `, cumulative rowcount = ${this.rowcount.sum()}`;
						}
						console.log(this.hint);
						if (rowcount && this.repeat) {
							if (this.rowsOfSQL > 1) {
								this.$parent.offset[0] = this.$parent.offset[1];
								this.$parent.execute=true;
								location.href = this.$parent.$refs.update.href_update;
							}
							else {
								this.dblclick(event);
							}
							return;
						}
						else {
							setAttribute(this, 'sql', `rowcount = ${rowcount}`);	
						}
					}
					
					this.wait = false;
				}
			}
		},
		
		mouseout_p(event){
			var self = event.target;
			var hover = self.parentElement.querySelector('.hover');
			hover.style.display = 'none';
		},
		
		mouseover_p(event){
			var self = event.target;
			var hover = self.parentElement.querySelector('.hover');
			hover.style.display = "block";
			hover.style.left = event.pageX || event.clientX + document.body.scroolLeft;
			hover.style.top = event.pageY || event.clientY + document.body.scrollTop;				
		},
		
		async keydown(event){
			if (event.target.tagName == 'TEXTAREA'){
				switch (event.key){
				case 'S':
				case 's':
					if (!event.ctrlKey)
						break;
					event.preventDefault();
					
					var sql = event.target.value;
					var rowcount = await this.query(sql.replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">"));
					this.hint = 'click to copy the text or press Insert to edit the content';					
					this.edit = false;
					setAttribute(this, 'sql', sql);
					console.log(`rowcount of ${sql} = ${rowcount}`);
					break;
				}
			}
			else{
				switch (event.key){
				case 'Insert':
					event.preventDefault();
					
					this.edit = true;
					this.rows = 10;
					this.cols = 128;
					break;
				}				
			}
		},
		
		input_textarea(event){
			var sql = event.target.value;
			//console.log(sql);
			var text = JSON.parse(eval("[" + sql.match(/replace into (?:\._\w+)+ *\(\w+(?:, \w+)*\) *values *\((.*)\);$/)[1] + "]")[1]);
			this.$parent.data[0].text = text;	
		},
		
	},    
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(textarea, binding) {
		    	textarea.scrollTop = textarea.scrollHeight;
		    	textarea.focus();
		    },
		},

		click: {
		    // after dom is inserted into the document
		    mounted(target, binding) {
		    	var self = binding.instance;
		    	if (self.execute)
		    		self.dblclick({target});		    		
		    },
		},
	},		
	
}

</script>

<style>
span.hover {
	display: none;
	color: red;
	transform: translate(4em, -100%);
	position: absolute;
	z-index: 10;
}

p.update {
	overflow-x: hidden;
}

</style>