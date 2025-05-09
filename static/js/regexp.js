// a legal open bracket is represented by
var openBracket = "(?<![\\\\])\\[";

// a non-open-bracket char is represented by :
var nonOpenBracket = "(?:(?<=[\\\\])\\[|[^\\[])";

// a non-bracket char is represented by :
var nonBracket = "(?:[^\\[\\]]|(?<=[\\\\])\\[|(?<=[\\\\])\\])";

// a legal Close bracket is represented by
var CloseBracket = "(?<![\\\\])\\]";

// a non-Close-bracket char is represented by :
var nonCloseBracket = "(?:(?<=[\\\\])\\]|[^\\]])";

// any symbol to be matched outside the paired brackets:
// firstly, a legal open bracket is detected and, before the legal open bracket there are no brackets;
// .(?=${nonBracket}*${openBracket})

// secondly, no legal Close brackt is detected: //all not
// .(?=${nonCloseBracket}*$)
// put together:
var outsidePairedBrackets = `(?=${nonBracket}*${openBracket}|${nonCloseBracket}*$)`;

// symbol inside the paired brackets:
var insidePairedBrackets = `(?=${nonOpenBracket}*${CloseBracket})`;

var leftParenthesisForCapture = `(?<![\\\\])\\((?!(?:\\?<=|\\?<!|\\?=|\\?!|\\?:))${outsidePairedBrackets}`;

function need_escape(s) {
    switch (s) {
    case "(":
    case ")":
    case "{":
    case "}":
        return true;
    default:
        return false;
    }
}

function recursive_construct(parentheses, depth) {
    var mid = parentheses.length / 2;
    var start = parentheses.slice(0, mid);

    var end = parentheses.slice(mid);
    if (need_escape(start)) {
        start = "\\" + start;
        end = "\\" + end;
    }

    if (depth == 1)
        return `${start}[^${parentheses}]*${end}`;

	var recursive = recursive_construct(parentheses, depth - 1);
    return `${start}[^${parentheses}]*(?:${recursive}[^${parentheses}]*)*${end}`;
}

function balancedGroups(parentheses, depth, multiple) {
	if (multiple == null)
		multiple = '*';

    var regex = recursive_construct(parentheses, depth);
    if (multiple)
        return `((?:${regex})${multiple})`;
    else {
		return `(${regex})`;
	}
}

export function balancedBraces(depth) {
	var multiple = '';
	if (depth.isString) {
		if (depth.back() == '.') {
			depth = depth.length;
		}
		else {
			multiple = depth.back();
			depth = depth.length - 1;
		}

		depth = 1 << depth - 1;
	}

    return balancedGroups("{}", depth, multiple);
}

function balancedParentheses(depth, multiple) {
	if (multiple == null)
		multiple = '';
    return balancedGroups("()", depth, multiple);
}

function balancedBrackets(depth, multiple) {
	if (multiple == null)
		multiple = false;
    return balancedGroups("\\[\\]", depth, multiple);
}

function remove_lookaround(regex) {
    return regex.replace(/\(\?=[^(]+?\)|\(\?![^(]+?\)|\(\?<=[^(]+?\)|\(\?<![^(]+?\)/g, "");
}

export function balanced_match(pairs, text, depth) {
	depth ||= 16;
	switch (pairs) {
    case '()':
        return text.match(balancedParentheses(depth));

    case '[]':
        return text.match(balancedBrackets(depth));

    case '{}':
        return text.match(balancedBraces(depth));

    default:
    	return text.match(balancedGroups(pairs, depth, ''));
    }
}

export function balanced_matchAll(pairs, text, depth) {
	depth ||= 16;
	switch (pairs) {
    case '()':
        return text.matchAll(new RegExp(balancedParentheses(depth), "g"));

    case '[]':
        return text.matchAll(new RegExp(balancedBrackets(depth), "g"));

    case '{}':
        return text.matchAll(new RegExp(balancedBraces(depth), "g"));

    default:
    	return text.matchAll(new RegExp(balancedGroups(pairs, depth, ''), "g"));
    }
}

export function remove_capture(regex){
    // (?<=), (?<!), (?=), (?!), (?:)
    return regex.replace(new RegExp(leftParenthesisForCapture, 'g'), "(?:");
}


console.log('import regexp.js');
