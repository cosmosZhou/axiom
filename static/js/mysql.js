console.log('import mysql.js');

export function	is_string(Type){
	return Type.match(/varchar\(\d+\)|text/);
}	

export function	is_json(Type){
	return Type.match(/json/);
}

export function	is_number(Type){
	return Type.match(/int|double/);
}

export function	is_int(Type){
	return Type.match(/int/);
}

export function	is_float(Type){
	return Type.match(/double/);
}
	
export function	is_enum(Type){
	var m = Type.match(/enum\((\S+)\)/);
	if (!m)
		return;
	var option = m[1].split(",");	
	return option.map(el => el.slice(1, -1));
}

export async function show_tables(database, host, user, token) {
	var sql = `show tables in ${database}`;
	//console.log({sql});
	return (await query(host, user, token, sql)).map(table => table[`Tables_in_${database}`]);
}

export async function show_full_columns(database, table, host, user, token){
	if (database)
		table =	`${database}.${table}`;

	var desc = await query(host, user, token, `show full columns from ${table}`);
	var dtype = {};
	var transform = {};
	var style_entity = {};
	var api = {};
	var comments = {};
	for (var {Field, Type, Comment} of desc){
		dtype[Field] = {};
		var option = is_enum(Type);
		if (option){
			dtype[Field] = option;
		}
		else if (is_int(Type)){
			dtype[Field] = 'int';
		}
		else if (is_float(Type)){
			dtype[Field] = 'float';
		}
		else if (is_json(Type)){
			dtype[Field] = 'json';
		}
		else{
			dtype[Field] = 'string';
		}
		
		if (Comment) {
			var data = JSON.parse(Comment);
			if (data.transform) {
				transform[Field] = data.transform;
			}
			else if (data.url && data.inputs) {
				api[Field] = data;
			}
			else if (Comment.match(/"color: \w+; background: \w+"/)){
				data.null = 'color: gray; background: pink',
				style_entity[Field] = data;
			}
			else {
				comments[Field] = data;
			}
		}
	}
	
	return {desc, dtype, transform, style_entity, api, Comment: comments};
}

export function parse_statement(name, kwargs){
	var sql = [];
	if (kwargs.with) {
		sql.push(...parse_expression([...name, 'with'], kwargs.with));	
	}
	
	var {select} = kwargs;
	if (kwargs.set) {
		var {set, update} = kwargs;
		if (set.isArray) {
			for (var [i, set] of enumerate(set)) {
				sql.push(...parse_expression([...name, 'set', i], set));	
			}
		}
		else {
			sql.push(...parse_expression([...name, 'set'], set));
		}
		
		sql.push(...parse_expression([...name, 'update'], update));
	}
	else {
		if (select) {
			if (select.isArray) {
				for (var [i, select] of enumerate(select)) {
					sql.push(...parse_expression([...name, 'select', i], select));
				}
			} 
			else {
				sql.push(...parse_expression([...name, 'select'], select));
			}
		}
	    
	    var {from} = kwargs;
	    if (from.from) {
	        sql.push(...parse_statement([...name, 'from'], from));
	    }
	    else {
			sql.push(...parse_expression([...name, 'from'], from));
		}

		if (kwargs.inner_join) {
			sql.push(...parse_expression([...name, 'inner_join'], kwargs.inner_join));
		}
		else if (kwargs.left_join) {
			sql.push(...parse_expression([...name, 'left_join'], kwargs.left_join));
		}
		else if (kwargs.right_join) {
			sql.push(...parse_expression([...name, 'right_join'], kwargs.right_join));
		}
		else if (kwargs.cross_join) {
			sql.push(...parse_expression([...name, 'cross_join'], kwargs.cross_join));
		}
		else if (kwargs.full_join) {
			sql.push(...parse_expression([...name, 'full_join'], kwargs.full_join));
		}
	}
	    

	var {where} = kwargs;
	if (where)
    	sql.push(...parse_expression([...name, 'where'], where));
    
    var {group, order} = kwargs;
    if (group) {
		sql.push(...parse_expression([...name, 'group'], group));
		
		var {having} = kwargs;
		if (having) {
			sql.push(...parse_expression([...name, 'having'], having));
		}
    } 
    
    if (order) {
		sql.push(...parse_expression([...name, 'order'], order));
    }
    
    var {limit, offset} = kwargs;
    if (limit)
    	sql.push(...parse_expression([...name, 'limit'], limit));
    
    if (offset)
    	sql.push(...parse_expression([...name, 'offset'], offset));
        
   return sql;
}

function wrap_args(args, name, func) {
	for (var [i, arg] of enumerate(args)) {
		for (var arg of arg) {
			arg.name.unshift(...name, func, i);
		}
	}
	
	var ret = [];
	for (var arg of args) {
		ret.push(...arg);
	}
	
	return ret;
}

function wrap_arg(arg, name, func) {
	var ret = [];
	for (var arg of arg) {
		arg.name.unshift(...name, func);
		ret.push(arg);
	}

	return ret;
}

function wrap_args_skip(args, name, func) {
	if (args.length > 1) {
		for (var [i, arg] of enumerate(args)) {
			for (var arg of arg) {
				arg.name.unshift(...name, func, i);
			}
		}
	}
	else if (args.length == 1){
		var [arg] = args;
		for (var arg of arg) {
			arg.name.unshift(...name);	
		}
	}
	
	var ret = [];
	for (var arg of args) {
		ret.push(...arg);
	}
	
	return ret;
}

export function parse_expression(name, cond){
    if (cond == null)
        return [];

    if (cond.isNumber)
		return [{name, value: cond}];

    if (cond.isString) {
		if (cond)
			return [{name, value: cond}];
		return [];
	}

	if (cond.from) {
		return parse_statement(name, cond);
	}
	
	if (cond.isArray) {
		var sql = [];
		for (var [i, cond] of enumerate(cond)) {
			sql.push(...parse_expression([...name, i], cond));
		}
		
		return sql;
	}
	
    var [func] = Object.keys(cond);

	if (!func)
		return [];
		
    if (cond[func].isArray) {
		var args = cond[func].map(cond => parse_expression([], cond));
	}
    else
        var args = [parse_expression([], cond[func])];

    switch (func) {
    case 'and':
    case 'or':
    	args = args.filter(arr => arr.length);
    	return wrap_args_skip(args, name, func);
    	
    case 'eq':
    case 'ne':
    case 'gt':
    case 'lt':
    case 'ge':
    case 'le':
    case 'add':
    case 'sub':
    case 'mul':
    case 'div':
    case 'mod':
    case 'AND':
    case 'XOR':
    case 'right_shift':
    case 'left_shift':

    case 'regexp_binary':
    case 'like_binary':
    case 'not_regexp':
    case 'not_like':
    case 'not_regexp_binary':
    case 'not_like_binary':
    case 'regexp':
    case 'like':
    case 'as':

    case 'json_extract':
    case 'json_extract_unquote':
        if (args.any(arr => !arr.length)) {
			return [];
		}
		return wrap_args(args, name, func);
		
    case 'invert':
    case 'distinct':
        if (args.any(arr => !arr.length)) {
			return [];
		}
    	return wrap_arg(args[0], name, func);
        
    case 'regexp_like':
    case 'not_regexp_like':
        if (!args[1] || !args[1].length)
        	return [];
        	
    default:
        if (!args[0] || !args[0].length)
        	return [];

        while (!args.back().length)
        	args.pop();

		if (args.length == 1 && !cond[func].isArray) {
			return wrap_arg(args[0], name, func);
		}
    	return wrap_args(args, name, func);
    }
}

export var physic2logic = {
	eq: '=', 
	ne: '!=', 
	gt: '>', 
	lt: '<', 
	ge: '>=', 
	le: '<=', 
			
	invert: '~', 
			
	add: '+', 
	sub: '-', 
	mul: '*', 
	div: '/', 
	mod: '%', 
	AND: '&', 
	XOR: '^', 
	right_shift: '>>', 
	left_shift: '<<', 
			
	json_extract: '->', 
	json_extract_unquote: '->>', 
			
	regexp_binary: 'regexp binary', 
	like_binary: 'like binary', 
	not_regexp: 'not regexp', 
	not_like: 'not like', 
	not_regexp_binary: 'not regexp binary', 
	not_like_binary: 'not like binary', 
	not_regexp_like: 'not regexp_like', 
};

export var logic2physic = {};

for (var key in physic2logic) {
	logic2physic[physic2logic[key]] = key;
}

export function piece_together(kwargs) {
	return parse_statement([], kwargs).map(obj => {
		var {name, value} = obj;
		var [name, ...rest] = name;
		name += rest.map(arg => `[${arg}]`).join('');
		
		value = value.encodeURI();
		return `${name}=${value}`;
	});
}

export function get_cmd(kwargs) {
	if (kwargs.into)
		return 'insert';

	for (var cmd of ['select', 'update', 'delete', 'rename', 'revoke', 'grant', 'alter', 'show', 'drop', 'set']) {
		if (kwargs[cmd])
			return cmd;
	}
	
	return 'select';
}

export function simplify_expression(kwargs) {
	if (!kwargs)
		return;
		
	if (kwargs.isString || kwargs.isNumber)
		return;
		
	if (kwargs.where) {
		simplify_expression(kwargs.where);
		if (!len(kwargs.where)) {
			delete kwargs.where;
		}
		return;	
	}
	
	var entries = Object.entries(kwargs);
	if (!entries.length)
		return;

	var [[func, args]] = entries;
	var hit = false;
	switch (func) {
	case 'and':
	case 'or':
		deleteIndices(args, expr => {
			simplify_expression(expr);
			return !len(expr);
		});
		
		if (!args.length) {
			hit = true;
		}
		else if (args.length == 1){
			hit = true;
			Object.assign(kwargs, args[0]);
		}
		break;
	case 'eq':
	case 'ne':
	case 'gt':
	case 'lt':
	case 'ge':
	case 'le':
	case 'regexp':
	case 'like':
	case 'not regexp':
	case 'not like':
        for (var arg of args) {
			simplify_expression(arg);
		}
		
        if (!args[1] || !len(args[1]) || !args[0] || !len(args[0]))
			hit = true;
        	
        break;
    case 'order':
    case 'group_concat':
        for (var arg of args) {
			simplify_expression(arg);
		}
    
        if (!args[0] || !len(args[0]))
        	hit = true;
        	
		break;
	}
	
	if (hit) {
		delete kwargs[func];
	}
}

export function get_db_table(value) {
	if (value.isString || value.into || value.from || value.update)
		return {database: '', table: value};

	var entries = Object.entries(value);
	if (entries.length > 1) {
		return {database: '', table: value};
	}
	
	var [database, table] = entries[0];
	return {database, table};
}

export function set_cmd(value, old_cmd, new_cmd) {
	if (old_cmd == new_cmd)
		return;

	switch (new_cmd) {
	case 'select':
		switch (old_cmd) {
		case 'update':
			var from = value.update;
			delete value.update;
			delete value.set;
			break;
			
		case 'insert':
			var from = value.into;
			delete value.into;
			break;
			
		case 'delete':
			delete value.delete;
			var {from} = value;
			break;
			
		case 'set':
			var from = {corpus: 'markush'};
			delete value.set;
			break;
		}
		
		value.from = from;
		value.select = '*';
		break;

	case 'update':
		switch (old_cmd) {
		case 'select':
			var update = value.from;
			delete value.from;
			delete value.select;
			break;

		case 'insert':
			var update = value.into;
			delete value.into;
			break;
			
		case 'delete':
			var update = value.from;
			delete value.from;
			delete value.delete;
			break;
			
		case 'set':
			var update = {corpus: 'markush'};
			break;
		}

		value.update = update;
		if (!value.set)
			value.set = {eq: ['', '']};
		break;
		
	case 'insert':
		switch (old_cmd) {
		case 'select':
			var into = value.from;
			delete value.from;					
			break;
			
		case 'update':
			var into = value.update;
			delete value.update;
			delete value.set;
			break;
			
		case 'delete':
			var into = value.from;
			delete value.delete;
			delete value.from;					
			break;
			
		case 'set':
			var into = {corpus: 'markush'};
			delete value.set;
			break;
			
		}
		value.into = into;
		break;
		
	case 'delete':
		switch (old_cmd) {
		case 'select':
			var {from} = value;
			delete value.select;
			value.delete = true;
			break;
			
		case 'update':
			var from = value.update;
			delete value.update;
			delete value.set;
			break;
			
		case 'insert':
			var from = value.into;
			delete value.into;
			break;
			
		case 'set':
			var from = {corpus: 'markush'};
			delete value.set;
			value.delete = true;
			break;
		}
		
		value.from = from;
		break;

	case 'set':
		for (var key of Object.keys(value)) {
			delete value[key];
		}

		value.set = {eq: ['password', '']};
		break;

	case 'show':
		for (var key of Object.keys(value)) {
			delete value[key];
		}

		value.show = 'databases';
		break;

	case 'alter':
		switch (old_cmd) {
		case 'select':
			var {from} = value;
			for (var key of Object.keys(value)) {
				delete value[key];
			}

			value.alter = from;
			value.add = [['newField', 'text', '', '']];
			
			break;
			
		case 'update':
			var from = value.update;
			for (var key of Object.keys(value)) {
				delete value[key];
			}
			
			value.alter = from;
			value.add = [['newField', 'text', '', '']];
			
			break;
			
		case 'delete':
			var from = value.from;
			for (var key of Object.keys(value)) {
				delete value[key];
			}
			
			value.alter = from;
			value.add = [['newField', 'text', '', ]];
			break;
			
		case 'insert':
			var from = value.into;
			for (var key of Object.keys(value)) {
				delete value[key];
			}
			
			value.alter = from;
			value.add = [['newField', 'text', '', '']];
			break;
			
		case 'set':
			delete value.set;
			value.alter = {corpus: 'rlhf'};
			value.add = [['newField', 'text', '', '']];
			
			break;
		}

		break;
	}
}

export function normalize_desc(desc) {
	desc = {...desc};
	delete desc.Privileges;
	if (desc.Type == 'int(11)') {
		desc.Type = 'int';
	}
	delete desc.index;
}

export function modify_from_desc(database, table, desc) {
	var {Field, Type, Null, Comment, Extra} = desc;
	if (Null == 'NO') {
		Null = 'not null';
	}
	else {
		Null = '';
	}
	
	if (Comment) {
		Comment = `comment ${Comment.mysqlStr()}`;
	}
	return `alter table ${database}.${table} modify \`${Field}\` ${Type} ${Null} ${Extra} ${Comment}`;
}

export function add_column_from_desc(database, table, desc, after) {
	var {Field, Type, Null, Comment, Extra} = desc;
	Null = Null == 'NO' ? 'not null': '';

	if (Comment)
		Comment = `comment ${Comment.mysqlStr()}`;
	
	if (after == null)
		after = 'first';
	else
		after = `after ${after}`;

	return `alter table ${database}.${table} add column \`${Field}\` ${Type} ${Null} ${Extra} ${Comment} ${after}`;
}

export function change_from_desc(database, table, OldField, desc) {
	var {Field, Type, Null, Comment, Extra} = desc;
	if (Null == 'NO') {
		Null = 'not null';
	}
	else {
		Null = '';
	}
	
	if (Comment) {
		Comment = `comment ${Comment.mysqlStr()}`;
	}
	return `alter table ${database}.${table} change \`${OldField}\` \`${Field}\` ${Type} ${Null} ${Extra} ${Comment}`;
}

export var props = ['host', 'user', 'token', 'sql', 'data', 'kwargs', 'table'];