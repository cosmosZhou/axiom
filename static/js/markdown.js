
function close_star(text, status) {
    var tag_begin, tag_end;
    switch (Math.min(status.star_begin, status.star_end)) {
    case 1:
        tag_begin = '<i>';
        tag_end = '</i>';
        break;
    case 2:
        tag_begin = '<b>';
        tag_end = '</b>';
        break;
    default:
        tag_begin = '<b><i>';
        tag_end = '</i></b>';
        break;
    }
    if (status.star_begin < status.star_end)
        tag_end += '*'.repeat(status.star_end - status.star_begin);
    else if (status.star_begin > status.star_end)
        tag_begin = '*'.repeat(status.star_begin - status.star_end) + tag_begin;
    text = text.slice(0, status.star_index) + tag_begin + text.slice(status.star_index + status.star_begin, -status.star_end);
    delete status.star_begin;
    delete status.star_end;
    delete status.star_index;
    return text + tag_end;
}

export function postprocess_char(text, char, status) {
    var m;
    if (char == '*') {
        if (status.star_end == null) {
            if (status.star_begin == null) {
                status.star_begin = 0;
                status.star_index = text.length;
            }
            ++status.star_begin;
        }
        else if (status.star_begin)
            ++status.star_end;
    }
    else {
        if (status.star_begin) {
            if (status.star_end == null)
                status.star_end = 0;
            else if (status.star_end)
                text = close_star(text, status);
        }

        switch (char) {
        case ' ':
            if (status.star_begin && status.star_end == 0 && text.match(/\*+$/)) {
                delete status.star_begin;
                delete status.star_end;
                delete status.star_index;
            }

            if (status.code_lang);
            else if (m = text.match(/(?<=^|<br>|<\/h[1-6]>)#+$/)) {
                var h = m[0].length;
                if (1 <= h && h <= 6) {
                    text = text.slice(0, -h);
                    char = `<h${h}>` + char;
                    status.h = h;
                }
            }
            else if (m = text.match(/(?<=^|<br>|<\/h[1-6]>) *-$/)) {
                text = text.slice(0, -m[0].length);
                char = '&nbsp;'.repeat(m[0].length + 3) + char;
            }
            break;
        case "\n":
            [text, char] = clear_status(text, status);
            break;
        case '[':
        case '(':
            if (text.match(/(?<!\\)\\$/))
                status.latex_index = text.length - 1;
            break;
        case ')':
        case ']':
            if (text.match(/(?<!\\)\\$/)) {
                var {latex_index} = status;
                var html = render(text.slice(latex_index) + char);
                if (html) {
                    text = text.slice(0, latex_index);
                    char = html;
                }
                delete status.latex_index;
            }
            break;
        default:
            break;
        }
    }
    return text + char;
}

export function clear_status(text, status) {
    var m;
    var char = "\n";
    if (status.h) {
        char = `</h${status.h}>`;
        delete status.h;
    }
    else if (text.match(/(?<=^|<br>|<\/h[1-6]>)---$/)) {
        // <hr>
        text = text.slice(0, -3);
        char = '<hr>';
    }
    else if (m = text.match(/(?<=^|<br>|<\/h[1-6]>)```([a-zA-Z]+\d?)( *)$/)) {
        var code_lang = m[1];
        status.code_start = text.length - 3 - code_lang.length - m[2].length;
        status.code_index = text.length;
        status.code_lang = code_lang;
        char = '';
    }
    else if (status.code_lang) {
        if (m = text.match(/```$/)) {
            var {code_index, code_start, code_lang} = status;
            var code = text.slice(code_index, -3);
            code_lang = code_lang.toLowerCase();
            if (Prism.languages[code_lang])
                var code = Prism.highlight(code, Prism.languages[code_lang], code_lang);
            else 
                console.warn(`Language ${code_lang} not supported by Prism.js`);
            var html = `<pre class="language-${code_lang}" tabindex="8"><code class="language-${code_lang}">${code}</code></pre>`;
            text = text.slice(0, code_start) + html;
            delete status.code_lang;
            delete status.code_index;
            char = '<br>';
        }
    }
    else if ((m = text.match(/(?<=^|<br>|<\/h[1-6]>)\|([^|]*\|)+$/)) && !status.colgroup) {
        status.colgroup = [];
        text = text.slice(0, -m[0].length) + '<table border=1><tr style="text-align: center">' + m[0].slice(1, -1).split('|').map(cell => `<th>${cell.trim()}</th>`).join('');
        char = '</tr>';
    }
    else if ((m = text.match(/(?<=<\/tr>)\|([^|]*\|)+$/)) && status.colgroup) {
        var tr = m[0].slice(1, -1).split('|').map(cell => cell.trim());
        if (!status.colgroup.length && tr.every(cell => cell.match(/^:?-+:?$/))) {
            status.colgroup = tr.map(cell => cell.back() == ':' ? (cell[0] == ':'? 'center': 'right') : null);
            html = '';
            char = '';
        }
        else {
            var html = '<tr>';
            for (var i = 0; i < tr.length; ++i) {
                var cell = tr[i];
                var align = status.colgroup[i];
                if (align)
                    html += `<td style="text-align: ${align}">${cell}</td>`;
                else
                    html += `<td>${cell}</td>`;
            }
            char = '</tr>';
        }
        text = text.slice(0, -m[0].length) + html;
    }
    else if (status.colgroup) {
        delete status.colgroup;
        text += '</table>';
        char = '<br>';
    }
    else if (!status.latex_index)
        char = '<br>';
    if (status.star_begin) {
        // bold or italic text contains a newline?
        delete status.star_begin;
        delete status.star_end;
        delete status.star_index;
    }
    return [text, char];
}

export function postprocess_word(text, word, status) {
    for (var char of word)
        text = postprocess_char(text, char, status);
    return text;
}


console.log('import markdown.js');
