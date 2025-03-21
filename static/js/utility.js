"use strict";


function axiom_user() {
	var m = location.href.match(/([^\/]+)\/((?:index\.(?:php|html)|run\.py|php\/\w+\.php|\?)\b|$)/);
	return m && m[1];
}

function textFocused(text, selectionStart) {
	console.log("selectionStart = " + selectionStart);

	for (; selectionStart < text.length; ++selectionStart) {
		var char = text[selectionStart];
		if (char >= 'a' && char <= 'z' ||
			char >= 'A' && char <= 'Z' ||
			char == '_' ||
			char >= '0' && char <= '9') {
			continue;
		}
		else {
			break;
		}
	}

	var textForFocus = text.slice(0, selectionStart);
	var m = textForFocus.match(/(\w+)(?:\.\w+)*$/);
	return m[0];
}

function find_and_jump(event) {
	var self = event.target;

	var module = textFocused(self.value, self.selectionStart);
	console.log('module = ' + module);
	var href;
	var indexOfDot = module.lastIndexOf('.');
	var user = axiom_user();
	if (indexOfDot >= 0) {
		if (module.slice(indexOfDot + 1) == 'apply') {
			module = module.slice(0, indexOfDot);
			module += "&apply=0";
		}
		href = `/${user}/?module=${module}`;
	}
	else {
		switch (module) {
			case 'Algebra':
			case 'Calculus':
			case 'Discrete':
			case 'Geometry':
			case 'Neuro':
			case 'Set':
			case 'Probability':
				href = `/${user}/?module=${module}`;
				break;
			default:
				href = `/${user}/?symbol=${module}`;
		}
	}

	if (event.ctrlKey)
		location.href = href;
	else
		window.open(href);
}

function getDisplayMode(latex) {
	var displayMode = null;
	if (latex.slice(0, 2) == '\\[' && latex.slice(-2) == '\\]') {
		latex = latex.slice(2, -2);
		displayMode = true;
	}
	else if (latex.slice(0, 2) == '\\(' && latex.slice(-2) == '\\)') {
		latex = latex.slice(2, -2);
		displayMode = false;
	}
	return {displayMode, latex};
}

function render(latex) {
	try {
		var {displayMode, latex} = getDisplayMode(latex);
		if (displayMode !== null)
			return katex.renderToString(latex, { throwOnError: true, displayMode});
	} catch (error) {
		console.log(error);
	}
}

const latex = {
	// usage:
	// block latex:
	// <p v-latex>{{ "'\\[' + latex + '\\]'" }}</p>
	// <p v-latex="'\\[' + latex + '\\]'"></p>
	// <p v-latex.block="latex"></p>

	// inline latex:
	// <p v-latex>{{ "'\\(' + latex + '\\)'" }}</p>
	// <p v-latex="'\\(' + latex + '\\)'"></p>
	// <p v-latex.inline="latex"></p>
	mounted(el, binding) {
		var {value : latex} = binding;
		if (latex) {
			var {block, inline} = binding.modifiers;
			var displayMode = null;
			if (block)
				displayMode = true;
			else if (inline)
				displayMode = false;
			if (displayMode === null) {
				var {displayMode, latex} = getDisplayMode(latex);
				if (displayMode === null)
					return;
			}
			katex.render(latex, el, {
				displayMode,
				throwOnError: false,
				errorColor: "#ff0000"
			});
		}
		else {
			renderMathInElement(el, {
				delimiters: [
					{ left: "$$", right: "$$", display: true },
					{ left: "\\[", right: "\\]", display: true },
					{ left: "$", right: "$", display: false },
					{ left: "\\(", right: "\\)", display: false }
				],
				throwOnError: false,
				errorColor: "#ff0000"
			});
		}
	},
};

latex.updated = function(el, binding) {
	if (binding.oldValue === binding.value)
		return;
	latex.mounted(el, binding);
}


console.log("import utility.js");