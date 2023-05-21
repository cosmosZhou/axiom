from std import MySQL
from blueprint.debug import extract_latex, compile_definition_statement
from std.unicode import ascii2greek

keywords = ['False', 'None', 'True', 
            'and', 'as', 'assert', 'abs',
            'complex',
            'break', 
            'case', 'class', 'continue', 
            'def', 'del', 'dict', 
            'elif', 'else', 'enumerate', 'eval', 'exec', 'except', 'exp',  
            'finally', 'for', 
            'if', 'import', 'in', 'isinstance', 
            'len', 'list',
            'or', 
            'raise', 'range', 'return', 
            'self', 'set', 'super', 'sqrt',
            'try', 
            'while', 'with', 
            'yield']

keywords += ['axiom',
             'base',
             'countable', 'continuous',
             'deep',
             'differentiable'
             'empty', 'etype', 'evaluate', 'expand', 'expr',
             'finite', 'finiteset',
             'generate_var',
             'index', 'infinite', 'integer', 'integrable', 'invertible',
              
             'is_complex', 'is_continuous', 'is_contable', 'is_empty', 'is_integer', 'is_integrable', 'is_invertible', 
             'is_measurable', 'is_negative', 
             'is_nonempty', 'is_nonnegative', 'is_nonpositive', 'is_nonzero', 
             'is_positive', 'is_prime', 'is_real', 'is_singular', 'is_zero',
             
             'left_open', 
             'measurable', 
             'negative', 'nonempty', 'nonnegative', 'nonpositive', 'nonzero',
             'plausible', 'positive', 'prime', 'provable', 'proved'
             'real', 'right_open',
             'cup_finiteset', 'simplify', 'singular',
             'this',
             'uncountable', 
             'zero']

sections = ['algebra', 'calculus', 'discrete', 'geometry', 'keras', 'sets', 'stats']

from sympy import *
import sympy
import re
from axiom import *

def local_eval(python, __globals__):    
    try:
        result = eval(python, __globals__)
    except SyntaxError: 
        try:
            exec(python, __globals__)
        except Exception as e:
            return str(e)
    
        return ''

    except Exception as e:
        try:
            print(e)
            e = str(e)
            return e
        except:
            return str(type(e))        
    
    try:
        if hasattr(result, "is_Basic"):
            latex = r'\[%s\]' % result.latex
            if result.is_Boolean:
                __globals__['Eq'].append(result)
        else:
            latex = str(result)
            
            
    except Exception as e:
        print(e)
        latex = str(e)
        
    return latex
    
symbols = [symbol for symbol in sympy.__dict__ if re.match('^[A-Za-z]+$', symbol)]
    
def insert_into_hint():
    vocab = keywords + sections
    vocab += symbols
    
    vocab.remove('symbol')
    vocab.remove('function')
    vocab.remove('binomial')
    
#     print(vocab)
    
    data = []
    
    print('max len = ', max(len(v) for v in vocab))
    for word in vocab:
        length = len(word)
        for i in range(1, length - 1):
            data.append((word[:i], word, 1))
    
    for key, value, *_ in data:
        print(key, '=>', value)
        
    for s in {'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lamda', 'mu', 'nu', 'xi', 'omicron', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega'}:
        data.append((s, ascii2greek(s), 1))
        s = s.capitalize()
        data.append((s, ascii2greek(s), 1))
        s = s.upper()
        data.append((s, ascii2greek(s), 1))
        
    print(len(data))
    
    MySQL.instance.execute('delete from hint')
    MySQL.instance.load_data('hint', data)    
        
__globals__ = globals()    
def insert_into_debug():
    data = []
    for symbol in symbols:
#         if symbol != 'BandPart':
#             continue
        
        script = extract_latex(symbol)
        if not script:
            continue
        __locals__ = {**__globals__}        
        __locals__['Eq'] = []
        
        latex = []
        for line in script:
            latex.append(local_eval(compile_definition_statement(line), __locals__))
                            
        script = [s.replace('\\', r'\\').replace('"', '\\"') for s in script]
        latex = [s.replace('\\', r'\\').replace('"', '\\"') for s in latex]
        datum = (symbol, script, latex)
        print(datum)
        data.append(datum) 
            
    MySQL.instance.execute('delete from debug')
    
    print('len(data) =', len(data))
    MySQL.instance.load_data('debug', data)

if __name__ == '__main__':
    insert_into_hint()
    insert_into_debug()
