import os
from std.http import json_post
import ast
import tempfile
import json
import re
os.environ['MYSQL_HOST'] = '192.168.18.132'
os.environ['MYSQL_DATABASE'] = 'axiom'

# insert into latex (latex, python, training) select latex_.latex, latex_.python, latex_.training from latex right join latex_ using (latex) where latex.latex is null;
# update latex join latex_ using (latex) set latex.python = latex_.python where latex_.python != latex.python;

from std import MySQL

def ensure_correctness(table='latex_'):
    update_params = []
    delete_params = []
    for id, latex, python, training in MySQL.instance.select(table, fetch_size=10, limit=100000):
        obj = json_post('http://192.168.18.132:5000/eval', dict(python=python))
        if isinstance(obj, str):
            print(obj)
            print(python)
            delete_params.append((id,))
        elif 'latex' in obj:
            if obj['latex'] != latex:
                print(latex)
                print(obj['latex'])
                print(python)
                print()
                update_params.append((obj['latex'], id))
        elif 'error' in obj:
            print(obj['error'])
            print(python)
            delete_params.append((id,))
        else:
            print(obj)
            print(python)
            delete_params.append((id,))
            
    rowcount = MySQL.instance.executemany(f'update {table} set latex = %s where id = %s', update_params)
    print('rowcount =', rowcount)
        
    rowcount = MySQL.instance.executemany(f'delete from {table} where id = %s', delete_params)
    print('rowcount =', rowcount)
    
# from sympy import *

def debug():
    from std.file import Text
    python = []
    with open('error.txt', 'w+', encoding='utf8') as file:
        for line in Text('debug.txt'):
            print(line)
            if not line or re.match('offset = \d+', line):
                if python:
                    python = '\n'.join(python)
                    try:
                        latex = test(python)
                    except:
                        latex = ''

                    if not latex:
                        print(python + '\n\n', file=file)
                    python = []
            else:
                python.append(line)

from sympy import *

def test_file(python):
    if not python: 
        python = '''\
colorred_�� = Symbol(r"{\color{red} {��}}", real=True, shape=(oo,))
k = Symbol(positive=True, integer=True)
colorred_��[k] ** 2
'''
    lineno = ast.parse(python).body[-1].lineno - 1
    lines = python.split('\n')
    given, imply = lines[:lineno], lines[lineno:]
    given = '\n'.join(given)
    imply = '\n'.join(imply)
    
    python = f'''\
from sympy import *
{given}
obj = {imply}
print(sympify(obj).latex.encode())
'''
    with tempfile.NamedTemporaryFile(mode='w+', encoding='utf8', suffix='.py', delete=False) as file:
        file.write(python)
        file.file.flush()
        try:
            with os.popen(f'python {file.name} 2>&1') as buffer:
                latex = buffer.read().rstrip()
                latex = eval(latex).decode()
                print(json.dumps(dict(latex=latex), ensure_ascii=False))
        except:
            print(json.dumps(dict(error=latex), ensure_ascii=False))
        
    os.remove(file.name)
    return latex
    
def test_sft():
    error = 0
    count = 0
    # from model.gpt.sft import instance
    for id, latex, python, training in MySQL.instance.select('latex', fetch_size=10, limit=100000):
        count += 1
        text = latex + '\nPython codes yielding the latex above:\n'
        
        # result = dict(text=instance('facebook/opt-350m/latex', text))
        result = json_post('http://192.168.18.100:5001/generate/facebook/opt-350m/latex', dict(text=text))
        if isinstance(result, str):
            print(result)
        else:
            python_ = result['text']
            if python_ == python:
                continue
             
            print(python)
            print(python_)
            
        error += 1
        print(f'http://192.168.18.132:8000/axiom/query.php?user=prod&from[axiom]=latex&id={id}')
        print('acc:', (count - error) / count)
            
    print('acc:', (count - error) / count)
    
d, n = Symbol(domain=Range(2, oo))
y = Symbol(domain=Range(0, d), shape=(n,), random=True)
t = Symbol(integer=True)
obj = y[t] | y[t - 1]
print(obj.latex)
print(obj.python)

if __name__ == '__main__':
    # test_sft()
#     debug()
    ...
    # ensure_correctness()
    