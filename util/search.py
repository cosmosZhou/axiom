import os, re
from std.file import Text
from _collections import defaultdict

def axiom_directory():
    return os.path.dirname(os.path.dirname(__file__)) + '/Axiom'


def read_directory(root):
    for name in os.listdir(root):
        path = os.path.join(root, name)
        if os.path.isdir(path):
            yield path


def read_all_php(root):
    for directory in read_directory(root):
        for php in read_all_files(directory, '.php'):
            yield php


def read_all_py(root):
    for directory in read_directory(root):
        for py in read_all_files(directory, '.py'):
            yield py
            # if os.path.basename(py) != '__init__.py': 
                # yield py


def read_all_files(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            yield path
        elif os.path.isdir(path):
            yield from read_all_files(path, sufix)


def print_py(axiom, prefix=os.path.dirname(axiom_directory())):
    path = prefix + '/' + axiom.replace('.', '/')
    py = path + '.py'
    if not os.path.exists(py):
        py = path + '/__init__.py'
    print(py)

    
def print_all_plausibles():
    plausible = defaultdict(list)
    read_all_plausibles(plausible)
    
    prefix = os.path.dirname(axiom_directory())
    print('axioms plausible:')
    for section in plausible:
        for axiom in plausible[section]:
            print_py(axiom, prefix)


def axiom_provability(module):
    return eval(module).prove.__name__
    
    
def read_all_plausibles(plausible):
    count = 0
    for php in read_all_php(os.path.dirname(__file__)):
        path = php[:-3]
        py = php[:-3] + 'py'
        
        if not os.path.exists(py):
            py = path + '/__init__.py'
        
        if not os.path.exists(py):
            print(php + " is an obsolete file since its py file is deleted!")
            os.unlink(php)
            continue
    
        count += 1
        if is_axiom_plausible(php): 
            axiom = py_to_module(php)
            
            provability = axiom_provability(axiom)
            if provability in ('insurmountable', 'unprovable'):
                continue
            
            sec = section(axiom)    
            plausible[sec].append(axiom)


def section(axiom):
    return axiom.split('.', 3)[0]


def is_axiom_plausible(php):
    for statement in yield_from_mysql(php):
        matches = is_latex(statement)
        for match in matches:
            if re.compile(".+tag\*\{(\?=.+)\}.+").search(match[0]):
                return True
            
    return False

    
def is_latex(latex): 
    return re.compile('\\\\\[.+?\\\\\]').finditer(latex)


def get_extension(file):
    return os.path.splitext(file)[-1]    

    
def module_to_py(theorem):
    full_theorem_path = module_to_path(theorem)
    py = full_theorem_path + ".py"
    if not os.path.exists(py):
        py = full_theorem_path + '/__init__.py'

    return py


def module_to_path(theorem):
    theorem = theorem.replace(".", "/")
    return os.path.dirname(os.path.dirname(__file__)) + f"/Axiom/{theorem}"

    
def py_to_module(py, delimiter='.'):
    module = []
    pythonFile = py
    while True:
        dirname = os.path.dirname(pythonFile)
        basename = os.path.basename(pythonFile)
        if basename == 'Axiom':
            break
        
        module.append(basename)
        pythonFile = dirname

    module[0] = module[0][:-len(get_extension(module[0]))]
    
    module.reverse()

    if module[-1] == '__init__':
        module.pop()
    
    module = delimiter.join(module)
    return module


def yield_from_mysql(php):
    for statement in Text(php):
        if not statement.startswith(r"//"):
            continue

        statement = statement[2:]
        yield statement


def search(keyword, caseSensitive=True, wholeWord=False, regularExpression=False): 
    modules = []
    for php in read_all_py(os.path.dirname(__file__)):
        module = py_to_module(php)
#         print(module)
        if not caseSensitive:
            if wholeWord:
                if re.compile(r'\b%s\b' % keyword, re.I).search(module):
                    modules.append(module)
                    
            elif regularExpression:
                if re.compile(keyword, re.I).search(module):
                    modules.append(module)

            else:
                if keyword.tolower() in module.tolower():
                    modules.append(module)

        elif wholeWord:
            if re.compile(r'\b%s\b' % keyword).search(module):
                modules.append(module)
                
        elif regularExpression:
            if re.compile(keyword).search(module):
                modules.append(module)
        else:
            if keyword in module: 
                modules.append(module)
    
    prefix = os.path.dirname(axiom_directory())
    
    print("in all, there are %d hits:" % len(modules))
    for module in modules:
        print_py(module, prefix)

    
def is_py_theorem(py):
    for line in Text(py):
        if not line:
            continue
        if re.match('from util import \*', line):
            return True
        assert re.match('from \. import \w+', line), py
        return False
    
def yield_callee_from_py(py):
    prove = False
    for line in Text(py):
#         print("line =", line)
        if re.match('^def prove\(', line):
            prove = True
            continue

        if prove:
            if re.match(r'^    return\b', line):
                break
            
            if re.match('^ *#', line):
                continue
            
            for m in re.finditer(r'\b(?:Algebra|Sets|Calculus|Discrete|Geometry|Keras|Stats)(?:\.\w+)+', line):
                module = m[0]        
                m = re.match('(.+)\.apply$', module)
                if m:
                    module = m[1]
    #             print("module =", module)
                yield module
        
def is_def_start(funcname, statement):
    return re.match(f"def +{funcname}\([^)]*\) *: *", statement)
        
def analyze_apply(py, i):
    count = len(py)
    provability = None
    while i < count:
        statement = py[i]
        if is_def_start('prove', statement):
            break

        if matches := re.match('@prove(.+)', statement):
            if matches := re.match('\((.+)=(.+)\)', matches[1]):
                provability = matches[1]
            
        i += 1

    return i, provability

def match_section(statement):
    return re.findall(r'\b(?:Algebra|Sets|Calculus|Discrete|Geometry|Keras|Stats)(?:\.\w+)+', statement)

def yield_from_py(module):
    python_file = module_to_py(module)

    [*py] = Text(python_file)
    count = len(py)

    i = 0
    while i < count:
        statement = py[i]
        if matches := re.match('from +(.+) +import +(.*)', statement):
            prefix, namespaces = matches.groups()
            namespaces = [s for s in re.split("[\s,]+", namespaces) if s]

            if namespaces and namespaces[-1] == '\\':
                namespaces.pop()
                i += 1
                statement = py[i]

                namespaces_addition = [s for s in re.split("[\s,]+", statement) if s]

                namespaces += namespaces_addition
            i += 1
            continue
        
        if matches := re.match('import +(.+)', statement):
            packages = matches[1]
            packages = [s for s in re.split("\s*,\s*", packages) if s]

            for package in packages:
                package = [s for s in re.split("\s+", package) if s]
                match len(package):
                    case 1:
                        package, = package
                    case _:
                        ...
            i += 1
            continue

        if is_def_start('apply', statement):
            yield {
                'line' : i
            }

            i, provability = analyze_apply(py, i)

            yield {
                'line' : i,
                'provability' : provability
            }

            break
        i += 1
    i += 1

    if i < count:
        statement = py[i]
        if matches := re.match('    from Axiom import (.+)', statement):
            section = matches[1].split(", ")
            yield {
                'line' : i,
                'section' : section
            }
            i += 1

        while i < count:
            statement = py[i]
            statement = statement.rstrip()
            # skip empty lines
            if re.match('\s*$', statement):
                i += 1
                continue

            # the start of the next global statement other than def prove
            if re.match('\w', statement):
                break

            # stop analyzing if return statement is encountered.
            if re.match('    return\b.*$', statement):
                statement = statement.rstrip()
                statement = statement[4:]

                yield {
                    'line' : i,
                    'unused' : True,
                    'statement' : statement
                }

                i += 1
                while i < count:
                    statement = py[i]

                    statement = statement.rstrip()
                    # skip empty lines
                    if re.match('\s*', statement):
                        i += 1
                        continue

                    # the start of the next global statement other than def prove
                    if re.match('\w', statement):
                        break

                    obj = {
                        'line' : i,
                        'unused' : True
                    }

                    if matches := re.match('\s*#(.*)', statement):
                        obj['comment'] = True
                        obj['statement'] = "#" + matches[1].lstrip()
                    else:
                        statement = statement[4:]
                        obj['statement'] = statement
                        
                    yield obj
                    i += 1
                break
            
            obj = {
                'line' : i
            }
            # cope with comments starting with #
            if matches := re.match('\s*#(.*)', statement):
                obj['comment'] = True
                obj['statement'] = "#" + matches[1].lstrip()

                yield obj
                i += 1
                continue

            statement = statement[4:]

            obj['statement'] = statement

            if re.search('(=|<<) *apply\(', statement):
                obj['module'] = py_to_module(python_file)
                        
            elif matches := match_section(statement):
                index = 0

                dict = {}
                for module in matches:
                    if module.endswith('.apply'):
                        module = module[:-6]
                    
                    index = statement.index(module, index)
                    dict[index] = module
                    index += len(module)
                
                obj['a'] = dict

            yield obj
            i += 1

        while i < count:
            statement = py[i]
            statement = statement.rstrip()
            # cope with comments starting with #
            if matches := re.match('\s*#(.*)', statement):
                if matches := re.search('(created|updated) on (\d\d\d\d-\d\d-\d\d)', matches[1]):
                    yield {
                        'line' : i,
                        'comment': True,
                        'statement': '',
                        matches[1] : matches[2] 
                    }

            i += 1
        
def yield_function_from_py(py):
    # prove = False
    for line in Text(py):
#         print("line =", line)
            
        if m := re.match('(?:    )+from Axiom((?:\.\w+)+) import (\w+)', line):
            callee, func = m.groups()
            callee = callee[1:]
            print(callee, func)        
            yield callee, func
        
def detect_and_change():
    for py in read_all_py(axiom_directory()):
        lines = Text(py).collect()
        regex = '    (\w+(?:, \w+)*) = (Symbol|Function)\((.+)\) *$'
        pivot = -1
        for i, line in enumerate(lines):
            if re.match('def prove', line):
                pivot = i
        
        if pivot < 0:
            continue
        
        for i, line in enumerate(lines):
            if i < pivot: 
                continue
            
            if m := re.match(regex, line):
                sym, func, kwargs = m.groups()
                
                syms = [sym]
                indices = []
                for j in range(1, 20):
                    try:
                        if m := re.match(regex, lines[i + j]):
                            sym_, func_, kwargs_ = m.groups()
                            if kwargs_ != kwargs or func != func_:
                                continue
                            syms.append(sym_)
                            indices.append(j)
                    except IndexError:
                        break
                    
                if not indices:
                    continue
                
                print(line)
                for j in indices:
                    print(lines[i + j])
                    
                line = '    %s = %s(%s)' % (', '.join(syms), func, kwargs)
                lines[i] = line
                
                indices.reverse()
                for j in indices:
                    del lines[i + j]
                
                print('after  deleting:', len(lines))
                print(line)
                print(py)
                print()
                print()
                print()
                Text(py).writelines(lines)
                
                break
        
        
if __name__ == '__main__':
    detect_and_change()
    exit()
#     keyword = 'subs'

    keyword = ''
    caseSensitive = True
    wholeWord = False
    wholeWord = True
    regularExpression = False
#     regularExpression = True
    
    if keyword:
        search(keyword, caseSensitive, wholeWord, regularExpression)
    else: 
        print_all_plausibles()
