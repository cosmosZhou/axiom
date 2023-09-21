"use strict";

function InitMathJax(miniseconds) {
	return {
	    startup: {
	        ready(){
	              console.log('MathJax is loaded, but not yet initialized');
	              MathJax.startup.defaultReady();
	              console.log('MathJax is initialized, and the initial typeset is queued');
	              
	              MathJax.startup.promise.then(() => {                    
	                  console.log('MathJax initial typesetting complete');
	                  setTimeout(() => {
	                	  var p = document.querySelectorAll('p');
	                	  if (p.length) {
	                          for (let p of document.querySelectorAll('p')){
	                              if (p.innerText.startsWith("\\[")) {
	                                  console.log("unfinished work detected!");
	                                  console.log(p.innerText);
	                                  console.log('trying MathJax.typesetPromise() again;');
	                                  MathJax.typesetPromise();
	                                  break;
	                              }
	                          }
	                      }
	                	  else {
	                    	  console.log("no p tags have been detected!");
	                    	  setTimeout(() => {
	                    		  console.log("MathJax.typesetPromise() due to absence of p tags");
	                    		  MathJax.typesetPromise();
	                    	  }, miniseconds);
	                	  }
	                  }, miniseconds);
	              });                  
	         }
	      },
	
	    tex: {
	        maxBuffer: 60 * 1024,       // maximum size for the internal TeX string (10K)
	        //reference: http://docs.mathjax.org/en/latest/options/input/tex.html?highlight=MAXBUFFER#the-configuration-block
	    },
	};	
}

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
		href = `/${user}/index.php?module=${module}`;
	}
	else {
		switch (module) {
			case 'algebra':
			case 'calculus':
			case 'discrete':
			case 'geometry':
			case 'keras':
			case 'sets':
			case 'stats':
				href = `/${user}/index.php?module=${module}`;
				break;
			default:
				href = `/${user}/index.php?symbol=${module}`;
		}
	}

	if (event.ctrlKey)
		location.href = href;
	else
		window.open(href);

}
