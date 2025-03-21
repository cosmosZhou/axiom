"use strict";

export function mounted(self) {
	document.addEventListener(
		'mousedown', 
		function(e) {
			if (e.button === 0) {
				console.log('Left mouse button clicked in document');
				self.click_left(e);
			}
		}
	);
}

export function click_left(event) {
	console.log("selectedIndex = ", this.selectedIndex);
	this.selectedIndex.clear();
}

export function fetch_code(lemma, proof) {
	var {comment, name, instImplicit, strictImplicit, implicit, given, explicit, imply: {lean: imply}} = lemma;
	if (!proof) {
		var {proof} = lemma;
		if (proof) {
			var by = proof.by ? 'by' : (proof.calc ? 'calc' : '');
			if (by)
				proof = proof[by];
			proof = proof.map(line => line.lean);
		}
	}
	if (comment)
		comment += '\n';
	else
		comment = '';
	var declspec = [];
	if (instImplicit) {
		if (!proof) {
			var alphaSet = {};
			for (var [, alpha] of instImplicit.matchAll(/\[\w+ ([\p{Script=Greek}a-zA-Z0-9_]+)\]/ug))
				alphaSet[alpha] = true;
			var alphaSet = Object.keys(alphaSet);
			declspec.push(`  {${alphaSet.join(' ')} : Type _}`);
		}
		declspec.push(instImplicit.replace(/^/mg, '  '));
	}
	if (implicit)
		declspec.push(implicit.replace(/^/mg, '  '));

	if (given) {
		declspec.push("-- given");
		given = given.map(line => line.lean.replace(/^/mg, '  '));
		declspec.push(...given);
	}

	if (explicit)
		declspec.push(explicit.replace(/^/mg, '  '));

	declspec = declspec.join("\n");

	imply = imply.replace(/^/mg, '  ');

	if (declspec)
		declspec = `\n${declspec}`;
	declspec += " :";

	if (proof) {
		proof = proof.map(code => {
			var {lean, latex} = code;
			code = lean.replace(/^/mg, '  ');
			if (latex)
				code += `\n  -- \\[${latex}\\]`;
			return code;
		});
		proof = proof.join("\n").ltrim("\n");
		proof = proof.rtrim();
		return `${comment}lemma ${name}${declspec}
-- imply
${imply}
-- proof
${proof}
`;
	}
	else
		return `${comment}axiom ${name}${declspec}
-- imply
${imply}
`;
}

console.log("import lemma.js");