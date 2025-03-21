
export const X_Ai_Engine = {
    deepseek: [
        'deepseek-v3',
        'deepseek-r1',
        'deepseek-chat',
        'deepseek-reasoner'
    ],
    azure: [
        'gpt-3.5-turbo',
        'gpt-3.5-turbo-1106',
        'gpt-3.5-turbo-16k',
        'gpt-4', 
    ],
    openai: [
        'gpt-4-turbo',
        'gpt-4o',
        'gpt-4o-mini',
        'gpt-4o-2024-11-20',
        'o1-preview',
        'o1-mini',
        'o1',
    ],
    anthropic: [
        'claude-3-sonnet',
        'claude-3-haiku',
        'claude-3-opus',
        'claude-3.5-sonnet',
        'claude-3.5-haiku'
    ],
    google: [
        'gemini-1.5-pro',
        'gemini-1.5-flash',
        'gemini-2.0-flash-exp',
    ],
    microsoft: [
        'phi-4',
    ],
};

const chat_template = `<|start_header_id|>%s<|end_header_id|>

%s<|eot_id|>`;

function apply_chat_template(message) {
    if (!message.isArray)
        message = [{role: 'user', content: message}];
    return message.map(message => chat_template.format(message.role, message.content)).join('') + chat_template.format('assistant', '%s').split('%s')[0];
}

function get_url(model, stream, repetition_penalty) {
    var temperature = null;
    var top_p = null;
    switch(model) {
    case 'o1-preview':
    case 'o1-mini':
        temperature = 1;
        top_p = 1;
    case 'deepseek-chat':
    case 'deepseek-reasoner':
        return {
            method: json_post,
            url: 'https://api.deepseek.com/chat/completions',
            data(message) {
                if (message.isArray)
                    var [message, messages] = [null, message];
                else
                    messages = null;
                return {
                    message,
                    messages,
                    model,
                    stream,
                };
            },
            header,
        };
    }
}

export async function generate(message, model, stream, Authorization, repetition_penalty) {
	console.log(`${model.toUpperCase()}: ${message.isString? message: JSON.stringify(message, null, 2)}`);
    var {method, url, data, header} = get_url(model, stream == null? false : true, repetition_penalty);
    var headers = {Authorization};

    if (header)
        Object.assign(headers, header);

    return await method(url, data(message), headers, stream);
}


export function parse_token(data) {
    if (data == 'finish' || data == '[DONE]')
        return;
    
    data = JSON.parse(data);
    var {choices, generated_text, token} = data;
    if (choices) {
        var [{delta: {content: text}}] = choices;
    }
    else {
        if (generated_text)
            return;
        var {text} = token;
    }
    return text;
}

console.log('import prompting.js');
