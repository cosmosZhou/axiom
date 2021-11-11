"use strict";

function $(selector){
	return document.querySelector(selector)
}

function get(url, data) {
	return axios.get(url, {params: data}).then(result => result.data);
}

function form_post(url, data) {
	return axios.post(url, Qs.stringify(data)).then(result => result.data);
}

function json_post(url, data) {
	return axios({
		url: url,
		method: 'post',
		data: data,
		header: {
			'Content-Type':'application/json'
		}
	}).then(result => result.data);
}

function ord(s) {
	return s.charCodeAt(0);
}

function chr(unicode) {
	return String.fromCharCode(unicode);
}

function strlen(s) {
	var length = 0;
	for (let i = 0; i < s.length; i++) {
		var code = s.charCodeAt(i)
		if (code < 128 || code == 0x2002) {
			if (code == ord('\t'))
				length += 4;
			else
				length += 1;
		}
		else
			length += 2;
	}
	return length;
}

function getParameter(name) {
	var reg = new RegExp("(^|&)" + name + "=([^&]*)(&|$)");
	var search = window.location.search;
	if (search.startsWith("?")) {
		var r = search.substr(1).match(reg);
		if (r != null)
			return unescape(r[2]);
	}
	return null;
}

String.prototype.format = function() {
	var args = arguments;
	var index = 0;
	return this.replace(/%s/g,
		function() {
			return args[index++];
		}
	);
};

String.prototype.capitalize = function() {
	return this[0].toUpperCase() + this.slice(1).toLowerCase();
};

String.prototype.ltrim = function() {
	return this.replace(/(^\s*)/g, "");
};

String.prototype.rtrim = function() {
	return this.replace(/(\s*$)/g, "");
};

NodeList.prototype.indexOf = function(e) {
	for (var i = 0; i < this.length; ++i) {
		if (this[i] == e)
			return i;
	}
	return -1;
};

NodeList.prototype.pop = function() {
	var lastChild = this[this.length - 1];
	lastChild.remove();
	return lastChild;
};

NodeList.prototype.shift = function() {
	var firstChild = this[0];
	firstChild.remove();
	return firstChild;
};

NodeList.prototype.reverse = function() {
	return [...this].reverse();
};

NodeList.prototype.splice = function(index, howmany) {
	var items = [...arguments].slice(2);
	var deletes = [];
	if (index < 0)
		index = this.length + index;

	var parent = this[0].parentElement;

	for (var i = index; i < index + howmany; ++i) {
		deletes.push(this[i]);
	}

	for (let node of deletes) {
		node.remove();
	}

	if (items) {
		if (index == this.length) {
			for (let item of items)
				parent.appendChild(item);
		}
		else {
			var pivot = this[index];
			for (let item of items)
				parent.insertBefore(item, pivot);
		}
	}

	return this;
};

NodeList.prototype.slice = function(start, end) {
	return [...this].slice(start, end);
};

HTMLCollection.prototype.slice = function(start, end) {
	var list = [...this];
	if (end < 0)
		end += list.length;

	if (start < 0)
		start += list.length;

	return list.slice(start, end);
};

HTMLCollection.prototype.indexOf = function(e) {
	for (var i = 0; i < this.length; ++i) {
		if (this[i] == e)
			return i;
	}
	return -1;
};

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Spread_syntax
HTMLCollection.prototype.splice = function(index, howmany) {
	var items = [...arguments].slice(2);
	var deletes = [];
	if (index < 0)
		index = this.length + index;

	var parent = this[0].parentElement;

	for (var i = index; i < index + howmany; ++i) {
		deletes.push(this[i]);
	}

	for (let node of deletes) {
		node.remove();
	}

	if (items) {
		if (index == this.length) {
			for (let item of items)
				parent.appendChild(item);
		}
		else {
			var pivot = this[index];
			for (let item of items)
				parent.insertBefore(item, pivot);
		}
	}

	return this;
};

Array.prototype.remove = function(index, size) {
	if (size == null)
		size = 1;
	return this.splice(index, size);
};

Array.prototype.resize = function(newSize,defaultValue) {
    while(newSize > this.length)
        this.push(defaultValue);
    this.length = newSize;
}

Array.prototype.insert = function(index, value) {
	if (index == this.length)
		return this.push(value);
	return this.splice(index, 0, value);
};

Array.prototype.back = function(val) {
	if (val == null)
		return this[this.length - 1];
	this[this.length - 1] = val;
};

/**
 * @template T
 */
class Queue {
	/**
	 * @param {Iterable<T>=} items The initial elements.
	 */
	constructor(items) {
		/** @private @type {T[]} */
		this._list = items ? Array.from(items) : [];
		/** @private @type {T[]} */
		this._listReversed = [];
	}

	/**
	 * Returns the number of elements in this queue.
	 * @returns {number} The number of elements in this queue.
	 */
	get length() {
		return this._list.length + this._listReversed.length;
	}

	isEmpty() {
		return !this.length;
	}
	/**
	 * Appends the specified element to this queue.
	 * @param {T} item The element to add.
	 * @returns {void}
	 */
	push(item) {
		this._list.push(item);
	}

	/**
	 * Retrieves and removes the head of this queue.
	 * @returns {T | undefined} The head of the queue of `undefined` if this queue is empty.
	 */
	pop() {
		if (this._listReversed.length === 0) {
			if (this._list.length === 0) return undefined;
			if (this._list.length === 1) return this._list.pop();
			if (this._list.length < 16) return this._list.shift();
			const temp = this._listReversed;
			this._listReversed = this._list;
			this._listReversed.reverse();
			this._list = temp;
		}
		return this._listReversed.pop();
	}

	/**
	 * Finds and removes an item
	 * @param {T} item the item
	 * @returns {void}
	 */
	delete(item) {
		const i = this._list.indexOf(item);
		if (i >= 0) {
			this._list.splice(i, 1);
		} else {
			const i = this._listReversed.indexOf(item);
			if (i >= 0) this._listReversed.splice(i, 1);
		}
	}

	[Symbol.iterator]() {
		let i = -1;
		let reversed = false;
		return {
			next: () => {
				if (!reversed) {
					i++;
					if (i < this._list.length) {
						return {
							done: false,
							value: this._list[i]
						};
					}
					reversed = true;
					i = this._listReversed.length;
				}
				i--;
				if (i < 0) {
					return {
						done: true,
						value: undefined
					};
				}
				return {
					done: false,
					value: this._listReversed[i]
				};
			}
		};
	}
}

function params(href) {
	var search;
	if (href != null) {
		search = href.slice(href.indexOf('?'));
	}
	else {
		search = location.search;
	}

	var kwargs = {};
	var query = search.substring(1);
	var vars = query.split("&");
	for (var i = 0; i < vars.length; ++i) {
		var pair = vars[i].split("=");
		kwargs[pair[0]] = pair[1];
	}

	return kwargs;
}

function* items(dict) {
	for (let k in dict) {
		yield [k, dict[k]];
	}
}

function join(sep, generator) {
	return list(generator).join(sep);
}

function list(generator) {
	var arr = [];
	for (let e of generator) {
		arr.push(e);
	}
	return arr;
}

function* map(fn, generator) {
	for (let e of generator) {
		yield fn(e);
	}
}



function cmp(x, y) {
	// If both x and y are null or undefined and exactly the same
	if (x === y) {
		return true;
	}

	// If they are not strictly equal, they both need to be Objects
	if (!(x instanceof Object) || !(y instanceof Object)) {
		return false;
	}

	// They must have the exact same prototype chain,the closest we can do is
	// test the constructor.
	if (x.constructor !== y.constructor) {
		return false;
	}

	for (var p in x) {
		// Inherited properties were tested using x.constructor ===
		// y.constructor
		if (x.hasOwnProperty(p)) {
			// Allows comparing x[ p ] and y[ p ] when set to undefined
			if (!y.hasOwnProperty(p)) {
				return false;
			}

			// If they have the same strict value or identity then they are
			// equal
			if (x[p] === y[p]) {
				continue;
			}

			// Numbers, Strings, Functions, Booleans must be strictly equal
			if (typeof (x[p]) !== "object") {
				return false;
			}

			// Objects and Arrays must be tested recursively
			if (!cmp(x[p], y[p])) {
				return false;
			}
		}
	}

	for (var p in y) {
		// allows x[ p ] to be set to undefined
		if (y.hasOwnProperty(p) && !x.hasOwnProperty(p)) {
			return false;
		}
	}
	return true;
};

function quote_mysql(param) {
	return param.replace(/'/g, "''").replace(/\\/, "\\\\");
}

function quote_html(param) {
	return param.replace(/&/g, "&amp;").replace(/'/g, "&apos;").replace(/\\/, "\\\\");
}

function str_html(param) {
	return param.replace(/&/g, "&amp;").replace(/<(?=[a-zA-Z!/])/g, "&lt;");
}

function quote(param) {
	return param.replace(/\\/, "\\\\").replace(/'/g, "\\'");
}

function isEnglish(ch) {
	return ch >= 'a' && ch <= 'z' || ch >= 'A' && ch <= 'Z' || ch >= 'ａ' && ch <= 'ｚ' || ch >= 'Ａ' && ch <= 'Ｚ'
                || ch >= '0' && ch <= '9' || ch >= '０' && ch <= '９';
}

function getClass(o) {
	return Object.prototype.toString.call(o).slice(8, -1);
}

function intersection(s1, s2) {
	var s = new Set();
	for (let e of s1) {
		if (s2.has(e)) {
			s.add(e);
		}
	}
	return s;
}

function deepCopy(obj) {
	var result, oClass = getClass(obj);

	if (oClass == "Object")
		result = {};
	else if (oClass == "Array")
		result = [];
	else
		return obj;

	for (var i in obj) {
		var copy = obj[i];

		if (getClass(copy) == "Object")
			result[i] = deepCopy(copy);
		else if (getClass(copy) == "Array")
			result[i] = deepCopy(copy);
		else
			result[i] = copy;
	}

	return result;
}


HTMLElement.prototype.getScrollTop = function() {
	var scrollTop = 0;

	var current = this;
	while (current !== null) {
		scrollTop += current.scrollTop;
		current = current.parentElement;
	}

	return scrollTop;
};

HTMLElement.prototype.getScrollLeft = function() {
	var scrollLeft = 0;

	var current = this;
	while (current !== null) {
		scrollLeft += current.scrollLeft;
		current = current.parentElement;
	}

	return scrollLeft;
}

function binary_search(arr, value, compareTo) {
    var begin = 0, end = arr.length;
    for (;;) {
        var mid = (begin + end) >> 1;
        if (begin == end)
            return -1;
            
        var ret = compareTo(arr[mid], value);
        if (ret < 0)
            begin = mid + 1;
        else if (ret > 0)
            end = mid;
        else
            return mid;
    }
}

function toUnicodeDigit(digits){
    var diff = ord('０') - ord('0');
    var ret = '';
    for (let i = 0; i < digits.length; ++i){
        ret += chr(ord(digits[i]) + diff);
    }
    return ret;
}