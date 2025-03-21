
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

            if (m = text.match(/(?<=^|<br>|<\/h[1-6]>)#+$/)) {
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
            else if (status.code_lang)
                char = '&nbsp;';
            break;
        case '\n':
            if (status.h) {
                char = `</h${status.h}>`;
                delete status.h;
            }
            else if (text.match(/(?<=<br>|^)---$/)) {
                // <hr>
                text = text.slice(0, -3);
                char = '<hr>';
            }
            else if (m = text.match(/(?<=<br>|^)```([a-zA-Z]+\d?)$/)) {
                var code_lang = m[1];
                status.code_index = text.length - 3 - code_lang.length;
                status.code_lang = code_lang;
            }
            else if (status.code_lang && (m = text.match(/(?<=<br>)```$/))) {
                var {code_index, code_lang} = status;
                var code = text.slice(code_index);
                var html = `<pre><code class="${code_lang}">${code}</code></pre>`;
                text = text.slice(0, code_index);
                char = html + '<br>';
                delete status.code_lang;
                delete status.code_index;
            }
            else if (!status.latex_index)
                char = '<br>';
            if (status.star_begin) {
                // bold or italic text contains a newline?
                delete status.star_begin;
                delete status.star_end;
                delete status.star_index;
            }
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

export function postprocess_word(text, word, status) {
    for (var char of word)
        text = postprocess_char(text, char, status);
    return text;
}


console.log('import markdown.js');
