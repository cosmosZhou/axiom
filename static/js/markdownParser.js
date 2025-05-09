// \$((?!new)\w+)

class AbstractParser {
    constructor(caret) {
        this.caret = caret;
    }

    get root() {
        return this.caret.root;
    }
}

class NewLineParser extends AbstractParser {
    constructor(caret) {
        super(caret);
        this.newline_count = 1;
        this.indent = 0;
    }

    parse(token) {
        switch (token) {
        case "\n":
            this.indent = 0;
            ++this.newline_count;
            return this;
        case ' ':
            ++this.indent;
            return this;
        case "\t":
            this.indent += 2;
            return this;
        default:
            var {caret, newline_count, indent} = this;
            return caret.parent.insert_newline(caret, newline_count, indent).parse(token);
        }
    }
}


class AmpParser extends AbstractParser {
    get html() {
        var {hash, name} = this;
        if (hash) {
            var {dec, hex} = hash;
            if (dec)
                return `&#${dec}`;
            if (hex)
                return `&#x${hex}`;
        }
        if (name)
            return `&${name}`;
    }

    badcase(token) {
        return this.caret.parent.insert_token(this.caret, this.html + token);
    }

    push_name(token) {
        var {name} = this;
        if (name) {
            if (name.length < 32) {
                name += token;
                return this;
            }
            return this.badcase(token);
        }
        this.name = token;
        return this;
    }

    parse(token) {
        // &(#[0-9]+|#x[0-9a-f]+|[^\t\n\f <&#;]{1,32});
        switch (token.toLowerCase()) {
        case "#":
            if (this.hash || this.name)
                break;
            this.hash = {};
            return this;
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
            if (this.hash) {
                if (this.hash.dec)
                    this.hash.dec += token;
                else if (this.hash.hex)
                    this.hash.hex += token;
                else
                    this.hash.dec = token;
            }
            else
                return this.push_name(token);
            return this;
        case 'x':
            if (this.hash) {
                if (this.hash.dec || this.hash.hex)
                    break;
                this.hash.hex = '';
            }
            else 
                break;
            return this;
        case 'a':
        case 'b':
        case 'c':
        case 'd':
        case 'e':
        case 'f':
            if (this.hash) {
                if (this.hash.dec || this.hash.hex == null)
                    break;
                this.hash.hex += token;
            }
            else
                return this.push_name(token);
            return this;
        case "\t":
        case "\n":
        case "\f":
        case ' ':
        case '<':
        case '&':
            break;
        case ';':
            var {caret} = this;
            delete this.caret;
            return caret.parent.insert_amp(caret, this);
        default:
            return this.push_name(token);
        }
        return this.badcase(token);
    }
}


class TagParser extends AbstractParser {
    constructor(caret) {
        super(caret);
        this.args = [];
    }

    get attrStr() {
        if (!this.attr)
            return '';
        return this.attr.map(args => {
            var [key, value, quote] = args;
            var leadingSpaces = ' '; // this might vary.
            return `${leadingSpaces}${key}=${quote}${value}${quote}`;
        }).join('');
    }

    get html() {
        var {type, name} = this;
        switch (type) {
        case 'TagBegin':
            return `<${name}${this.attrStr}`;
        case 'TagEnd':
            return `</${name}`;
        case 'VoidTag':
            return `<${name}${this.attrStr} /`;
        default:
            return '<';
        }
    }

    badcase(token) {
        return this.caret.parent.insert_token(this.caret, this.html + token);
    }

    parse(token) {
        // TagBegin
        // <([a-z][-:_a-z]*\d*)(?:\s+:?[a-z][-:_a-z]*(?:=(?:"[^"]*"|'[^']*'))?)*\s*>
        // TagEnd
        // <\/([a-z][-:_a-z]*\d*)>
        // VoidTag
        // <(img|mspace|br|input|span|meta|link)(?:\s+:?[a-z][-:_a-z]*(?:=(?:"[^"]*"|'[^']*'))?)*\s*\/>
        switch (token.toLowerCase()) {
        case "/":
            if (this.type)
                break;
            if (this.name)
                this.type = 'VoidTag';
            else {
                this.type = 'TagEnd';
                this.name = '';
            }
            return this;
        case 'a':
        case 'b':
        case 'c':
        case 'd':
        case 'e':
        case 'f':
        case 'g':
        case 'h':
        case 'i':
        case 'j':
        case 'k':
        case 'l':
        case 'm':
        case 'n':
        case 'o':
        case 'p':
        case 'q':
        case 'r':
        case 's':
        case 't':
        case 'u':
        case 'v':
        case 'w':
        case 'x':
        case 'y':
        case 'z':
            if (!this.name) {
                if (!this.type)
                    this.type = 'TagBegin';
                this.name = token;
                return this;
            }
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
            switch (this.type) {
            case 'TagBegin':
            case 'TagEnd':
                this.name += token;
                break;
            default:
                return this.badcase(token);
            }
            return this;
        case '>':
            var {caret} = this;
            delete this.caret;
            return caret.parent.insert_tag(caret, this);
        }
        return this.badcase(token);
    }
}


class Markdown {
    constructor(indent, parent) {
        this.parent = parent;
        this.args = [];
        this.kwargs = {indent};
    }

    get indent() {
        return this.kwargs.indent;
    }

    strArgs()
    {
        return this.args;
    }

    toString()
    {
        var s = this.strFormat().format(...this.strArgs());
        if (this.is_indented())
            s = ' '.repeat(this.indent) + s;
        return s;
    }

    get func() {
        return get_class(this);
    }

    is_indented() {
        return false;
    }

    insert_space(caret)
    {
        return this.parent.insert_space(this);
    }

    insert_star(caret)
    {
        console.log('insert_star is not defined', caret);
        return caret;
    }

    insert_token(caret, word)
    {
        return caret.push_token(word);
    }

    push_token(word)
    {
        return this.append(new MarkdownText(word, this.indent));
    }

    append($new)
    {
        if (this.parent)
            return this.parent.append($new);
        console.log('append is not defined', $new);
    }

    get root() {
        return this.parent.root;
    }

    toJSON() {
		return this.toString();
	}

    get bind() {
        return {
            args: this.args,
            kwargs : this.kwargs
        };
    }

    get previousElementSibling() {
        return this.parent.args[this.parent.args.indexOf(this) - 1];
    }

    append_left_bracket() {
        const indent = this.indent;
        const caret = new MarkdownCaret(indent);
        var $new = new MarkdownBracket(caret, indent);
        if (this.parent instanceof MarkdownDocument || this.parent instanceof MarkdownSPAN)
            this.parent.push($new);
        else 
            this.parent.replace(this, new MarkdownSPAN([this, $new], indent));
        return caret;
    }

    insert_right_bracket(caret)
    {
        return this.insert_token(caret, ']');
    }

    insert_right_parenthesis(caret)
    {
        return this.insert_token(caret, ')');
    }

    parse(token, callback) {
        if (callback)
            return callback(this, token);

        switch (token) {
        case ' ':
            return this.parent.insert_space(this);
        case "\n":
            return new NewLineParser(this);
        case '*':
            return this.parent.insert_star(this);
        case '[':
            return this.parent.insert_left_bracket(this);
        case ']':
            return this.parent.insert_right_bracket(this);
        case '(':
            return this.parent.insert_left_parenthesis(this);
        case ')':
            return this.parent.insert_right_parenthesis(this);
        case '<':
            return new TagParser(this);
        case '&':
            return new AmpParser(this);
        case "\t":
            token = '    ';
        default:
            return this.parent.insert_token(this, token);
        }
    }

    remove() {
        if (this.parent)
            this.parent.removeChild(this);
    }
}


class MarkdownCaret extends Markdown {
    is_indented() {
        return false;
    }

    strFormat()
    {
        return '';
    }

    append($new)
    {
        this.parent.replace(this, $new);
        return $new;
    }

    push_token(word)
    {
        var $new = new MarkdownText(word, this.indent);
        this.parent.replace(this, $new);
        return $new;
    }

    append_left_bracket() {
        const indent = this.indent;
        var caret = this;
        this.parent.replace(this, new MarkdownBracket(caret, indent));
        return caret;
    }
}

class MarkdownText extends Markdown {

    constructor(text, indent, parent = null)
    {
        super(indent, parent);
        this.kwargs.text = text;
    }

    get text() {
        return this.kwargs.text;
    }
    set text(text) {
        this.kwargs.text = text;
    }

    append($new)
    {
        if (this.parent)
            return this.parent.insert(this, $new);
        console.log('append is not defined', $new);
    }

    push_token(word)
    {
        this.text += word;
        return this;
    }

    is_indented() {
        return false;
    }

    strFormat()
    {
        return '%s';
    }

    strArgs()
    {
        return [this.text];
    }

    push_star() {
        var m;
        if (m = this.text.match(/\*([^*]*[^* \n\t])$/)) {
            this.text = this.text.slice(0, -m[0].length);
            var $new = new MarkdownText(m[1], this.indent);
            var I = new MarkdownI($new, this.indent);
            if (this.text) {
                if (this.parent instanceof MarkdownSPAN)
                    this.parent.push(I);
                else
                    this.parent.replace(this, new MarkdownSPAN([this, I], this.indent));
            }
            else
                this.parent.replace(this, I);
            return I;
        }
        if (this.parent instanceof MarkdownSPAN) {
            var THIS = this;
            var SPAN = this.parent;
            for (var i = SPAN.args.length - 2; i >= 0; --i) {
                var self = SPAN.args[i];
                if (self instanceof MarkdownText && (m = self.text.match(/\*([^*]*[^* \n\t])$/))) {
                    self.text = self.text.slice(0, -m[0].length);
                    var rest = ranged(i + 1, SPAN.args.length).map(j => SPAN.args[j]);
                    SPAN.args.splice(i + 1, SPAN.args.length - i - 1);
                    var span = new MarkdownSPAN(
                        [new MarkdownText(m[1], self.indent), ...rest],
                        self.indent
                    );
                    var I = new MarkdownI(span, self.indent, SPAN);
                    if (self.text)
                        SPAN.args[i + 1] = I;
                    else
                        SPAN.args[i] = I;
                    return THIS;
                }
            }
            if (SPAN.parent instanceof MarkdownI) {
                var B = SPAN.parent.toMarkdownB();
                if (B)
                    return B;
            }
        }
        this.text += '*';
        return this;
    }

    append_left_bracket() {
        if (this.text.match(/(?<!\\)(\\\\)*\\$/)) {
            this.text = this.text.slice(0, -1);
            var $new = this.parent.insert_Latex(this, true);
            if (!this.text)
                this.remove();
            return $new;
        }
        return super.append_left_bracket();
    }

    append_left_parenthesis() {
        if (this.text.match(/(?<!\\)(\\\\)*\\$/)) {
            this.text = this.text.slice(0, -1);
            var $new = this.parent.insert_Latex(this, false);
            if (!this.text)
                this.remove();
            return $new;
        }
        return super.append_left_parenthesis();
    }
}

class MarkdownArgs extends Markdown {
    constructor(args, indent, parent) {
        super(indent, parent);
        this.args = args;
        for (var arg of args)
            arg.parent = this;
    }
    
    replace(old, $new)
    {
        var i = this.args.indexOf(old);
        if (i < 0)
            throw new Error("replace is unexpected for " + get_class(this));

        if ($new.isArray) {
            this.args.splice(i, 1, $new);
            for (var el of $new) {
                if (!el.parent)
                    el.parent = this;
            }
        } else {
            this.args[i] = $new;
            if (!$new.parent)
                $new.parent = this;
        }
    }

    removeChild(node) {
        const i = this.args.indexOf(node);
        if (i < 0) {
            console.log(`removeChild is unexpected for ${get_class(this)}`);
            return;
        }
        this.args.splice(i, 1);
        if (this.args.length === 1) {
            const [arg] = this.args;
            const parent = this.parent;
            if (parent) {
                parent.replace(this, arg);
                arg.parent = parent;
            }
        }
    }

    push(arg) {
        this.args.push(arg);
        arg.parent = this;
    }

    unshift(arg) {
        this.args.unshift(arg);
        arg.parent = this;
    }

    strFormat()
    {
        return '';
    }

    insert_newline(caret, newlineCount, indent) {
        if (this.indent > indent) {
            return super.insert_newline(caret, newlineCount, indent);
        }
    
        if (this.indent < indent) {
            throw new Error(`${get_class(this)}::insert_newline is unexpected for ${get_class(this)}`);
        } else {
            for (let i = 0; i < newlineCount; ++i) {
                caret = new MarkdownCaret(indent);
                this.push(caret);
            }
            return caret;
        }
    }
    toJSON() {
        var dict = {};
        dict[this.func] = this.args.map(arg => arg.toJSON());
        return dict;
	}

    insert_Latex(caret, block) {
        var $new = new MarkdownCaret(this.indent);
        var latex = new MarkdownLatex($new, this.indent, block);
        if (caret instanceof MarkdownText)
            this.replace(caret, new MarkdownSPAN([caret, latex], this.indent));
        else {
            console.log('unknown context');
            this.push(latex)
        }
        return $new;
    }

    insert_H(caret, H) {
        if (this.parent)
            return this.parent.insert_H(this, H);
        console.log('insert_H is not defined', caret);
    }

    insert_UL(caret, m) {
        var indent = m[1].length;
        if (indent == this.indent + 1)
            indent = this.indent;
        caret.text = caret.text.slice(0, -m[0].length);
        var $new = new MarkdownCaret(indent);
        var LI = new MarkdownLI([$new], indent);
        var UL = new MarkdownUL([LI], indent);
        if (caret.text)
            this.push(UL);
        else
            this.replace(caret, UL);
        return $new;
    }

    insert_OL(caret, m) {
        var indent = m[1].length;
        if (indent > this.indent && indent < this.indent + 4)
            indent = this.indent;
        caret.text = caret.text.slice(0, -m[0].length);
        var $new = new MarkdownCaret(indent);
        var LI = new MarkdownLI([$new], indent);
        var OL = new MarkdownOL([LI], indent);
        if (caret.text)
            this.push(OL);
        else
            this.replace(caret, OL);
        return $new;
    }

    insert_TABLE(caret, m) {
        caret.text = caret.text.slice(0, -m[0].length);
        var {indent} = this;
        var $new = new MarkdownCaret(indent);
        var TH = m[0].trim().slice(1, -1).split('|').map(
            cell => new MarkdownTH(new MarkdownText(cell.trim(), indent), indent)
        );
        var TR = [
            new MarkdownTR(TH, indent), 
            $new
        ];
        var TABLE = new MarkdownTABLE(TR, indent);
        if (caret.text)
            this.push(TABLE);
        else
            this.replace(caret, TABLE);
        return $new;
    }

    insert_CODE(caret, m) {
        caret.text = caret.text.slice(0, -m[0].length);
        var lang = m[1];
        var $new = new MarkdownCaret(this.indent);
        var CODE = new MarkdownCODE($new, this.indent, lang);
        if (caret.text)
            this.push(CODE);
        else
            this.replace(caret, CODE);
        return $new;
    }
    
    insert_left_bracket(caret)
    {
        return caret.append_left_bracket();
    }

    insert_left_parenthesis(caret)
    {
        return this.insert_token(caret, '(');
    }

    insert_tag(caret, tag) {
        switch (tag.type) {
        case 'TagBegin':
        case 'VoidTag':
            var $new = new MarkdownCaret(this.indent);
            var tag = new MarkdownTag($new, this.indent, tag);
            if (caret instanceof MarkdownCaret)
                this.replace(caret, tag);
            else if (this instanceof MarkdownSPAN)
                this.push(tag);
            else
                this.replace(caret, new MarkdownSPAN([caret, tag], this.indent));
            return $new;
        case 'TagEnd':
            if (this instanceof MarkdownTag)
                return this;
            break;
        default:
            return this;
        }
    }
}


class MarkdownTag extends MarkdownArgs {
    constructor(arg, indent, kwargs, parent = null)
    {
        super([arg], indent, parent);
        var {name, type} = kwargs;
        this.name = name;
        this.is_void = type == 'VoidTag';
    }

    get name() {
        return this.kwargs.name;
    }
    set name(name) {
        this.kwargs.name = name;
    }

    get is_void() {
        return this.kwargs.is_void;
    }

    set is_void(is_void) {
        this.kwargs.is_void = is_void;
    }

    strArgs() {
        if (this.is_void)
            return [this.name, ...this.args];
        return [this.name, ...this.args, this.name];
    }

    strFormat()
    {
        var {is_void} = this;
        if (is_void) 
            return `<%s />`;
        var args = Array(this.args.length).fill('%s').join("\n");
        return `<%s>${args}</%s>`;
    }

    insert_space(caret) {
        return caret.push_token(' ');
    }

    insert_star(caret) {
        return caret.push_token('*');
    }

    insert_left_bracket(caret) {
        return caret.push_token('[');
    }

    insert_left_parenthesis(caret) {
        return caret.push_token('(');
    }

    insert_right_bracket(caret) {
        return caret.push_token(']');
    }

    insert_right_parenthesis(caret) {
        return caret.push_token(')');
    }

    insert_newline(caret, newlineCount, indent) {
        return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
    }

}


class MarkdownUnary extends MarkdownArgs {
    constructor(arg, indent, parent = null)
    {
        super([], indent, parent);
        this.arg = arg;
    }

    get arg() {
        return this.args[0];
    }

    set arg(arg) {
        this.args[0] = arg;
        arg.parent = this;
    }

    replace(old, $new)
    {
        console.assert(this.arg === old, new Error("assert failed: public function replace(\$old, \$new)"));
        this.arg = $new;
    }

    toJSON()
    {
        return this.arg.toJSON();
    }
}

class MarkdownA extends MarkdownArgs {
    get href() {
        return this.args[1];
    }

    is_indented() {
        return false;
    }

    strArgs() {
        return [this.href, this.args[0]];
    }

    strFormat()
    {
        return '<a href="%s">%s</a>';
    }

    insert_right_parenthesis(caret)
    {
        return this;
    }
}


class MarkdownI extends MarkdownUnary {
    is_token = true;
    is_indented() {
        return false;
    }

    strFormat()
    {
        return '<i>%s</i>';
    }

    append($new)
    {
        if (this.parent)
            return this.parent.insert(this, $new);
        console.log('append is not defined', $new);
    }

    push_token(word)
    {
        if (this.parent instanceof MarkdownSPAN || this.parent instanceof MarkdownLI) {
            word = new MarkdownText(word, this.indent);
            this.parent.push(word);
            return word;
        }
        console.log('push_token is not defined');
        return this;
    }

    toMarkdownB() {
        var caret = this;
        var parent = this.parent;
        var {previousElementSibling} = caret;
        if (previousElementSibling instanceof MarkdownText && previousElementSibling.text.endsWith('*')) {
            previousElementSibling.text = previousElementSibling.text.slice(0, -1);
            var B = new MarkdownB(caret.arg instanceof MarkdownB? caret.arg.arg: caret.arg, caret.indent);
            parent.replace(caret, B);
            if (!previousElementSibling.text)
                previousElementSibling.remove();
            return B;
        }
    }
}


class MarkdownB extends MarkdownUnary {
    is_token = true;
    is_indented() {
        return false;
    }

    strFormat()
    {
        return '<b>%s</b>';
    }
    append($new)
    {
        if (this.parent)
            return this.parent.insert(this, $new);
        console.log('append is not defined', $new);
    }

    push_token(word)
    {
        if (this.parent instanceof MarkdownSPAN || this.parent instanceof MarkdownLI) {
            word = new MarkdownText(word, this.indent);
            this.parent.push(word);
            return word;
        }
        console.log('push_token is not defined');
        return this;
    }

    toMarkdownI() {
        var caret = this;
        var parent = this.parent;
        var {previousElementSibling} = caret;
        if (previousElementSibling instanceof MarkdownText && previousElementSibling.text.endsWith('*')) {
            previousElementSibling.text = previousElementSibling.text.slice(0, -1);
            // text both italic and bold
            var I = new MarkdownI(caret, caret.indent);
            parent.replace(caret, I);
            if (!previousElementSibling.text)
                previousElementSibling.remove();
            return I;
        }
    }
}


class MarkdownCODE extends MarkdownUnary {
    is_Paragraph = true;
    constructor(caret, indent, lang) {
        super(caret, indent);
        this.kwargs.lang = lang;
    }

    get lang() {
        return this.kwargs.lang;
    }

    is_indented() {
        return false;
    }

    strArgs() {
        return [this.lang, this.lang, this.arg];
    }
    strFormat()
    {
        return '<pre class="language-%s"><code class="language-%s">%s</code></pre>';
    }

    insert_space(caret) {
        return caret.push_token(' ');
    }

    insert_star(caret) {
        return caret.push_token('*');
    }

    insert_left_bracket(caret) {
        return caret.push_token('[');
    }

    insert_left_parenthesis(caret) {
        return caret.push_token('(');
    }

    insert_right_bracket(caret) {
        return caret.push_token(']');
    }

    insert_right_parenthesis(caret) {
        return caret.push_token(')');
    }

    insert_newline(caret, newlineCount, indent) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/```$/)) {
                caret.text = caret.text.slice(0, -m[0].length);
                return this;
            }
        }
        return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
    }
}


class MarkdownH extends MarkdownArgs {
    constructor(caret, indent, level) {
        super([caret], indent);
        this.kwargs.level = level;
    }

    get level() {
        return this.kwargs.level;
    }

    is_indented() {
        return false;
    }

    strFormat()
    {
        var {level} = this;
        var hanging = Array(this.args.length - 1).fill('%s').join("\n");
        return `<h${level}>%s</h${level}>\n` + hanging;
    }

    get header() {  
        return this.args[0];
    }

    get hanging() {
        return this.args.slice(1);
    }

    insert_right(caret) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/\(([^)]+)/)) {
                var href = m[1];
                caret.text = caret.text.slice(0, -m[0].length);
            }
        }
        if (this.parent)
            return this.parent.insert_right(this, caret);
        console.log('insert_right is not defined', caret);
    }

    insert_space(caret)
    {
        if (caret instanceof MarkdownText) {
            if (caret === this.args.back()) {
                var m;
                if (m = caret.text.match(/(?<=\n|^)#+$/)) {
                    var level = m[0].length;
                    caret.text = caret.text.slice(0, -level);
                    var $new = this.insert_H(caret, level);
                    if (!caret.text)
                        caret.remove();
                    return $new;
                }
                if (m = caret.text.match(/(?<=\n|^)( *)[-*]$/))
                    return this.insert_UL(caret, m);
                if (m = caret.text.match(/(?<=\n|^)( *)\d+\.$/))
                    return this.insert_OL(caret, m);
            }
            caret.text += ' ';
        }
        return caret;
    }

    insert_star(caret) {
        if (caret instanceof MarkdownText)
            return caret.push_star();
        return this.insert_token(caret, '*');
    }

    insert_newline(caret, newlineCount, indent) {
        if (this.indent > indent)
            return super.insert_newline(caret, newlineCount, indent);
    
        if (this.indent < indent) {
            throw new Error(`${get_class(this)}::insert_newline is unexpected for ${get_class(this)}`);
        }

        if (caret === this.header) {
            caret = new MarkdownCaret(indent);
            this.push(caret);
            return caret;
        }
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/(?<=\n|^)```([a-zA-Z]+\d?)( *)$/))
                return this.insert_CODE(caret, m);
            if (newlineCount == 1) {
                if (m = caret.text.match(/(?<=\n|^) *\|([^|]*\|)+ *$/))
                    return this.insert_TABLE(caret, m);
                return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
            }
        }
        if (caret.is_Paragraph)
            return caret;
        var P = new MarkdownP(caret instanceof MarkdownSPAN? caret.args : [caret], this.indent);
        this.replace(caret, P);
        return P;
    }

    insert_token(caret, char)
    {
        if (caret instanceof MarkdownText || caret instanceof MarkdownCaret)
            return caret.push_token(char);
        var text = new MarkdownText(char, this.indent);
        if (caret.is_Paragraph)
            this.push(text);
        else if (caret instanceof MarkdownSPAN)
            caret.push(text);
        else
            this.replace(caret, new MarkdownSPAN([caret, text], this.indent));
        return text;
    }

    toJSON() {
        var dict = super.toJSON();
        dict['level'] = this.level;
		return dict;
	}

    insert(caret, $new)
    {
        console.assert(caret === this.args.back());
        if ($new instanceof MarkdownText) {
            if (caret instanceof MarkdownSPAN) {
                caret.push($new);
            }
            else {
                var texts = new MarkdownSPAN([caret, $new], this.indent);
                this.replace(caret, texts);
            }
            return $new;
        }
        else 
            throw new Error("assert failed: insert(caret, \$new) " + get_class(this));
    }

    insert_H(caret, level) {
        var $new = new MarkdownCaret(this.indent);
        var H = new MarkdownH($new, this.indent, level);
        if (level > this.level)
            this.push(H);
        else {
            var self = this;
            while (self.parent instanceof MarkdownH && level <= self.parent.level)
                self = self.parent;
            self.parent.push(H);
        }
        return $new;
    }
}


class MarkdownLatex extends MarkdownUnary {
    constructor(caret, indent, block) {
        super(caret, indent);
        this.kwargs.block = block;
    }

    get block() {
        return this.kwargs.block;
    }

    get is_Paragraph() {
        return this.block;
    }
    
    is_indented() {
        return false;
    }

    strFormat()
    {
        var {block} = this;
        if (block)
            return "\\[%s\\]";
        return "\\(%s\\)";
    }

    insert_space(caret) {
        return caret.push_token(' ');
    }

    insert_star(caret) {
        return caret.push_token('*');
    }

    insert_left_bracket(caret) {
        return caret.push_token('[');
    }

    insert_left_parenthesis(caret) {
        return caret.push_token('(');
    }

    insert_right_bracket(caret) {
        console.assert (caret instanceof MarkdownText);
        if (caret.text.match(/(?<!\\)(\\\\)*\\$/)) {
            if (!this.block)
                console.log('mismatched \\] for inline latex');
            caret.text = caret.text.slice(0, -1);
            return this;
        }
        return caret.push_token(']');
    }

    insert_right_parenthesis(caret) {
        console.assert (caret instanceof MarkdownText);
        if (caret.text.match(/(?<!\\)(\\\\)*\\$/)) {
            if (this.block)
                console.log('mismatched \\) for block latex');
            caret.text = caret.text.slice(0, -1);
            return this;
        }
        return caret.push_token(')');
    }

    insert_newline(caret, newlineCount, indent) {
        return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
    }
}


class MarkdownLI extends MarkdownArgs {
    is_indented() {
        return true;
    }

    strFormat()
    {
        return "<li>%s</li>".format(Array(this.args.length).fill('%s').join(""));
    }

    insert_newline(caret, newlineCount, indent) {
        if (caret instanceof MarkdownText) {
            caret.text += "\n".repeat(newlineCount) + ' '.repeat(indent);
            return caret;
        }
        caret = new MarkdownText("\n".repeat(newlineCount) + ' '.repeat(indent), indent);
        this.push(caret);
        return caret;
    }

    insert_LI(indent, ordered) {
        var $new = new MarkdownCaret(indent);
        var LI = new MarkdownLI([$new], indent);
        if (indent == this.indent)
            this.parent.push(LI);
        else if (indent > this.indent)
            this.push(ordered? new MarkdownOL([LI], indent) : new MarkdownUL([LI], indent));
        else {
            var self = this;
            while (indent < self.indent)
                self = self.parent.parent;
            self.parent.push(LI);
        }
        return $new;
    }

    insert_space(caret) {
        var m;
        if (caret instanceof MarkdownText) {
            if (m = caret.text.match(/\n( *)[-*]$/)) {
                var indent = m[1].length;
                if (indent == this.indent + 1)
                    indent = this.indent;
                caret.text = caret.text.slice(0, -m[0].length);
                return this.insert_LI(indent, false);
            }
            if (m = caret.text.match(/\n( *)\d+\.$/)) {
                var indent = m[1].length;
                if (indent > this.indent && indent < this.indent + 4)
                    indent = this.indent;
                caret.text = caret.text.slice(0, -m[0].length);
                return this.insert_LI(indent, true);
            }
            if (m = caret.text.match(/(?<=\n|^)#+$/)) {
                var level = m[0].length;
                caret.text = caret.text.slice(0, -level);
                return this.insert_H(caret, level);
            }
        }
        return caret.push_token(' ');
    }

    insert_star(caret) {
        if (caret instanceof MarkdownText) {
            var $new = this.try_escape_li(caret, '*');
            if ($new)
                return $new;
            return caret.push_star();
        }
        return this.insert_token(caret, '*');
    }

    try_escape_li(caret, word) {
        var self = this;
        var {text} = caret;
        var m;
        if (text.match(/\n\n$/)) {
            var ol_match = word.match(/^ *\d+\.?/);
            var ul_match = word.match(/^ *[-*]/);
            var preprocess = caret => word;
        }
        else if (m = text.match(/\n\n *[-*]$/)) {
            var ol_match = false;
            var ul_match = word.match(/^ +/);
            var preprocess = caret => {
                caret.text = caret.text.slice(0, -m[0].length);
                return m[0] + word;
            };
        }
        else 
            return;

        while (self && self.parent) {
            if (self.parent.parent instanceof MarkdownLI) 
                self = self.parent.parent;
            else {
                if (self.parent instanceof MarkdownOL && !ol_match || self.parent instanceof MarkdownUL && !ul_match)
                    return self.parent.parent.insert_token(self.parent, preprocess(caret));
                    
                break;
            }
        }
    }

    insert_token(caret, word) {
        if (caret instanceof MarkdownText) {
            var $new = this.try_escape_li(caret, word);
            if ($new)
                return $new;
        }
        return super.insert_token(caret, word);
    }
}

// unordered list
class MarkdownUL extends MarkdownArgs {
    is_Paragraph = true;
    is_indented() {
        return false;
    }
    strFormat()
    {
        return "<ul>\n%s\n</ul>".format(Array(this.args.length).fill('%s').join("\n"));
    }
}


// ordered list
class MarkdownOL extends MarkdownArgs {
    is_Paragraph = true;
    is_indented() {
        return false;
    }

    strFormat()
    {
        return "<ol>\n%s\n</ol>".format(Array(this.args.length).fill('%s').join("\n"));
    }
}


class MarkdownTD extends MarkdownUnary {
    is_indented() {
        return false;
    }

    get textAlign() {
        return this.kwargs.textAlign;
    }

    set textAlign(textAlign) {
        this.kwargs.textAlign = textAlign;
    }

    strFormat()
    {
        var {textAlign} = this;
        if (textAlign)
            return `<td style="text-align: ${textAlign}">%s</td>`;
        return '<td>%s</td>';
    }
}

class MarkdownTH extends MarkdownUnary {
    is_indented() {
        return false;
    }

    get textAlign() {
        return this.kwargs.textAlign;
    }

    set textAlign(textAlign) {
        this.kwargs.textAlign = textAlign;
    }

    strFormat()
    {
        var {textAlign} = this;
        if (textAlign)
            return `<th style="text-align: ${textAlign}">%s</th>`;
        return '<th>%s</th>';
    }
}

class MarkdownTR extends MarkdownArgs {
    is_indented() {
        return false;
    }

    strFormat()
    {
        return '<tr>%s</tr>'.format(Array(this.args.length).fill('%s').join(""));
    }
}

class MarkdownTABLE extends MarkdownArgs {
    is_Paragraph = true;
    is_indented() {
        return false;
    }

    strFormat()
    {
        return '<table>%s</table>'.format(Array(this.args.length).fill('%s').join("\n"));
    }

    insert_space(caret)
    {
        if (caret instanceof MarkdownText)
            caret.text += ' ';
        else 
            return caret.push_token(' ');
        return caret;
    }

    insert_newline(caret, newlineCount, indent) {
        if (caret instanceof MarkdownText && newlineCount >= 1) {
            var m;
            if (m = caret.text.fullmatch(/ *\|([^|]*\|)+ */)) {
                var {indent} = this;
                var $new = new MarkdownCaret(indent);
                var TH = m[0].trim().slice(1, -1).split('|').map(
                    cell => cell.trim()
                );

                if (newlineCount == 1 && this.args.filter(arg => arg instanceof MarkdownTR).length == 1 && TH.every(cell => cell.fullmatch(/:?-+:?/))) {
                    var colgroup = TH.map(cell => cell.back() == ':' ? (cell[0] == ':'? 'center': 'right') : (cell[0] == ':'? 'left': null));
                    for (var [textAlign, th] of zip(colgroup, this.args[0].args))
                        th.textAlign = textAlign;
                    this.replace(caret, $new);
                }
                else {
                    var TD = TH.map(
                        cell => new MarkdownTD(new MarkdownText(cell, indent), indent)
                    );
                    for (var [td, th] of zip(TD, this.args[0].args))
                        td.textAlign = th.textAlign;
                    var TR = new MarkdownTR(TD, indent);
                    this.replace(caret, TR);
                    if (newlineCount > 1)
                        this.parent.push($new);
                    else 
                        this.push($new);
                }
                return $new;
            }
        }
        return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
    }
}


class MarkdownSPAN extends MarkdownArgs {
    is_indented() {
        return false;
    }
    strFormat()
    {
        return '<span>%s</span>'.format(Array(this.args.length).fill('%s').join(""));
    }

    insert_space(caret)
    {
        console.assert(!(caret instanceof MarkdownCaret));
        console.assert(caret === this.args.back());
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/(?<=\n|^)#+$/)) {
                var level = m[0].length;
                caret.text = caret.text.slice(0, -level);
                if (!caret.text)
                    caret.remove();
                return this.parent.insert_H(this, level);
            }
            if (m = caret.text.match(/(?<=\n|^)( *)[-*]$/))
                return this.insert_UL(caret, m);
            if (m = caret.text.match(/(?<=\n|^)( *)\d+\.$/))
                return this.insert_OL(caret, m);
            caret.text += ' ';
        }
        else {
            var caret = new MarkdownText(' ', this.indent);
            this.push(caret);
        }
        return caret;
    }

    insert_star(caret) {
        if (caret instanceof MarkdownI) {
            var B = caret.toMarkdownB();
            if (B)
                return B;
        }
        else if (caret instanceof MarkdownB) {
            var I = caret.toMarkdownI();
            if (I)
                return I;
        }
        else if (caret instanceof MarkdownText) {
            if (this.parent instanceof MarkdownLI) {
                var $new = this.parent.try_escape_li(caret, '*');
                if ($new)
                    return $new;
            }
            return caret.push_star();
        }
        return this.insert_token(caret, '*');
    }

    insert_newline(caret, newlineCount, indent) {
        if (newlineCount == 1 || this.parent instanceof MarkdownLI)
            return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
        var P = new MarkdownP(this.args, this.indent);
        this.parent.replace(this, P);
        return P;
    }

    insert(caret, $new)
    {
        console.assert(caret === this.args.back());
        console.assert ($new instanceof MarkdownText);
        console.assert (!(caret instanceof MarkdownText));
        this.push($new);
        return $new;
    }

    append($new) {
        if ($new instanceof MarkdownText) {
            this.push($new);
            return $new;
        }
        return this.parent.append($new);
    }

    insert_Latex(caret, block) {
        var $new = new MarkdownCaret(this.indent);
        var latex = new MarkdownLatex($new, this.indent, block);
        if (caret instanceof MarkdownText)
            this.push(latex);
        else {
            console.log('unknown context');
            this.push(latex)
        }
        return $new;
    }

    insert_UL(caret, m) {
        var indent = m[1].length;
        if (indent == this.indent + 1)
            indent = this.indent;
        caret.text = caret.text.slice(0, -m[0].length);
        var self = this.parent;
        if (self instanceof MarkdownLI)
            return self.insert_LI(indent);

        var $new = new MarkdownCaret(indent);
        var LI = new MarkdownLI([$new], indent);
        var UL = new MarkdownUL([LI], indent);
        if (caret.text)
            this.push(UL);
        else
            this.replace(caret, UL);
        return $new;
    }

    insert_OL(caret, m) {
        var indent = m[1].length;
        if (indent == this.indent + 1)
            indent = this.indent;
        caret.text = caret.text.slice(0, -m[0].length);
        var self = this.parent;
        if (self instanceof MarkdownLI)
            return self.insert_LI(indent, true);

        var $new = new MarkdownCaret(indent);
        var LI = new MarkdownLI([$new], indent);
        var OL = new MarkdownOL([LI], indent);
        if (caret.text)
            this.push(OL);
        else
            this.replace(caret, OL);
        return $new;
    }

    insert_token(caret, word)
    {
        if (caret instanceof MarkdownText && this.parent instanceof MarkdownLI) {
            var $new = this.parent.try_escape_li(caret, word);
            if ($new)
                return $new;
        }
        return super.insert_token(caret, word);
    }

    insert_left_parenthesis(caret)
    {
        if (caret instanceof MarkdownBracket)
            return caret.append_left_parenthesis();
        return super.insert_token(caret, '(');
    }
}


class MarkdownP extends MarkdownSPAN {
    is_Paragraph = true;
    strFormat()
    {
        return '<p>%s</p>'.format(Array(this.args.length).fill('%s').join(""));
    }
}

class MarkdownPairedGroup extends MarkdownUnary {
    is_indented() {
        return false;
    }

    insert_newline(caret, newline_count, indent) {
        return super.insert_newline(caret, newline_count, indent);
    }

    insert(caret, func) {
        if (this.arg === caret) {
            if (caret instanceof LCaret) {
                this.arg = new func(caret, this.indent);
                return caret;
            }
        }
        throw new Error(`insert is unexpected for ${get_class(this)}`);
    }
}


class MarkdownBracket extends MarkdownPairedGroup {
    is_token = true;
    strFormat() {
        return '[%s]';
    }

    append_left_bracket() {
        const indent = this.indent;
        const caret = new MarkdownCaret(indent);
        var $new = new MarkdownBracket(caret, indent);
        if (this.parent instanceof MarkdownSPAN)
            this.parent.push($new);
        else
            this.parent.replace(this, new MarkdownSPAN([this, $new], indent));
        return caret;
    }

    append_left_parenthesis() {
        const indent = this.indent;
        const caret = new MarkdownCaret(indent);
        var $new = new MarkdownA([this.arg, caret], indent);
        this.parent.replace(this, $new);
        return caret;
    }

    insert_space(caret) {
        return this.insert_token(caret, ' ');
    }

    insert_right_bracket(caret) {
        return this;
    }
}


class MarkdownDocument extends MarkdownArgs {
    is_indented() {
        return false;
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join("\n");
    }

    insert_space(caret)
    {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/(?<=\n|^)#+$/)) {
                var level = m[0].length;
                caret.text = caret.text.slice(0, -level);
                var $new = this.insert_H(caret, level);
                if (!caret.text)
                    caret.remove();
                return $new;
            }
            if (m = caret.text.match(/(?<=\n|^)( *)[-*]$/))
                return this.insert_UL(caret, m);
            if (m = caret.text.match(/(?<=\n|^)( *)\d+\.$/))
                return this.insert_OL(caret, m);
            caret.text += ' ';
        }
        return caret;
    }

    get root() {
        return this;
    }

    insert_star(caret) {
        if (caret instanceof MarkdownText)
            return caret.push_star();
        return this.insert_token(caret, '*');
    }

    insert_newline(caret, newlineCount, indent) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/(?<=\n|^)```([a-zA-Z]+\d?)( *)$/))
                return this.insert_CODE(caret, m);
            if (newlineCount == 1 && (m = caret.text.match(/(?<=\n|^) *\|([^|]*\|)+ *$/)))
                return this.insert_TABLE(caret, m);
        }
        if (newlineCount > 1) {
            caret = new MarkdownText("\n".repeat(newlineCount - 1) + ' '.repeat(indent), this.indent);
            this.push(caret);
            return caret;
        }
        return this.insert_token(caret, "\n".repeat(newlineCount) + ' '.repeat(indent));
    }

    insert_H(caret, level) {
        var $new = new MarkdownCaret(this.indent);
        this.push(new MarkdownH($new, this.indent, level));
        return $new;
    }

    insert_token(caret, char)
    {
        var text = new MarkdownText(char, this.indent);
        if (caret.is_token) {
            var $new = new MarkdownSPAN([caret, text], this.indent);
            this.replace(caret, $new);
        }
        else if (caret.is_Paragraph)
            this.push(text);
        else
            return super.insert_token(caret, char);
        return text;
    }

    insert_left_bracket(caret) {
        if (caret instanceof MarkdownText) {
            var $new = new MarkdownCaret(this.indent);
            this.replace(caret, new MarkdownSPAN([caret, new MarkdownBracket($new, this.indent)], this.indent));
            return $new;
        }
        return super.insert_left_bracket(caret);
    } 
}


export default class StreamedParser {
    constructor(generator) {
        var caret = new MarkdownCaret(0);
        this.caret = caret;
        this.root = new MarkdownDocument([caret], 0);
        this.generator = generator;
    }

    parse(token, callback) {
        this.caret = this.caret.parse(token, callback);
        // if (this.caret.root !== this.root) 
        //     console.log('caret.root !== this.root');
    }

    get html() {
        return this.root.toString();
    }

    build() {
        for (var token of this.generator)
            this.parse(token);
    }
}

console.log('import markdownParser.js');
