#!/usr/local/python3/bin/python3
#!/home/lizhi/python/bin/python

import os, sys, re
from std import batch_map, rindex

from std.file import Text
from os.path import dirname, basename, realpath, isdir, join, sep, exists

try:
    import axiom
except ImportError as e:
    from util.utility import source_error
    error_message, line = source_error()

    m = re.fullmatch(r'File "([^"]+(?:\\|/)(?:\w+)\.py)", line (\d+), in <module>', error_message)
    assert m, error_message
    file, line_number = m.groups()

    line_number = int(line_number) - 1
    print('file =', file)
    print('line_number =', line_number)
    assert 'site-packages' not in file

    file = Text(file)

    lines = file.readlines()
    del lines[line_number]

    file.writelines(lines)

    command = 'python ' + ' '.join(sys.argv)
    print(command)

    exit_code = os.system(command)
    print('exit_code =', exit_code)
    exit(exit_code)

import time
from multiprocessing import cpu_count
from queue import PriorityQueue
from functools import singledispatch
import random
from util.utility import RetCode

def axiom_directory():
    directory = dirname(__file__)
    if not directory:
        return './axiom'
    return directory + '/axiom'


class Globals:
    count = 0

    @classmethod
    def increment_count(cls):
        cls.count += 1

    plausible = []

    failed = []

    data = []
    

def readFolder(rootdir, sufix='.py'):
    names = os.listdir(rootdir)
    unused = 0
    for name in names:
        path = join(rootdir, name)

        if path.endswith(sufix):
            name = name[:-len(sufix)]
            if name == '__init__':
                line = Text(path).readline()
                if not line:
                    
                    lines = Text(path).readlines()
                    for i, line in enumerate(lines):
                        if line:
                            break
                    else:
                        i = len(lines)

                    if not i:
                        removeFile(path)
                        continue
 
                    try:
                        lines = lines[i:]
                        Text(path).writelines(lines)
                    except UnboundLocalError:                        
                        removeFile(path)
                        continue
                    
                if re.match('from *\. *import +\w+', line):
                    continue

                path = path[:-len(sufix) - len('/__init__')]
                if not any(name not in ('__pycache__', '__init__.py') for name in os.listdir(path)):
                    __init__ = path + '/__init__.py'
                    print(__init__, "has no children, thus reducing to a normal module file.")
                    try:
                        os.rename(__init__, path + '.py')
                    except PermissionError as e:
                        print(e)
            else: 
                path = path[:-len(sufix)]

            paths = re.split(r'[\\/]+', path)
#             print(path)
            index = rindex(paths, 'axiom')

            package = '.'.join(paths[index + 1:])

            Globals.increment_count()
            
            yield package

        elif isdir(path):
            if name == '__pycache__':
                unused += 1
            else:
                yield from readFolder(path, sufix)
        else:
            unused += 1

    if unused == len(names):
        print(f"removing empty directory {rootdir}")
        import shutil
        shutil.rmtree(rootdir)                
            

def project_directory():
    return dirname(axiom_directory())


def working_directory():
    return dirname(project_directory())


def create_module(package, module):
    print('package =', package)
    print('module =', module)
    
    __init__ = project_directory() + sep + package.replace('.', sep) + sep + '__init__.py'
    file = Text(__init__)
    
    for line in file:
        m = re.match('from \. import (\w+(?:, *\w+)*)', line)
        if m and module in m[1].split(', *'):
            print('module', module, 'is already added in', package)
            return True
    
    print('editing', __init__)
    addition = 'from . import '
    addition += module
    
    if file.size and not file.endswith('\n'):
        addition = '\n' + addition
    file.append(addition)


def run(package, debug=True):
    args = (project_directory() + sep + 'run.py', package)
    if debug:
        return os.system('python %s %s debug=True' % args)
    else: 
        try:
            return os.popen('python %s %s' % args).readlines()
        except UnicodeDecodeError as e:
            print(e)

    
def import_module(package):
    try:
        module = axiom
        for attr in package.split('.'):
            module = getattr(module, attr)
        return module
    
    except AttributeError as e: 
        print(e)
        m = re.fullmatch("module '([\w\.]+)' has no attribute '(\w+)'", str(e))
        assert m
        create_module(*m.groups())
        print(package, 'is created newly')
        return -1


def prove_with_timing(module, **kwargs):
    lapse = time.time()
    state, latex = module.prove(**kwargs)
    lapse = time.time() - lapse
    return state, lapse, latex


def tackle_type_error(package, debug=True):
    module = import_module(package)
    from types import ModuleType
    if not isinstance(module, ModuleType) and not module.is_FunctionClass:
        return
    
    print("package =", package)
    index = package.rindex('.')
    __init__ = package[:index]
    func = package[index + 1:]
    __init__ = import_module(__init__)
    __init__ = __init__.__file__
    print("__init__.__file__ =", __init__)
    
    file = Text(__init__)
    index = file.find('from . import ' + func, False)
    if index < 0:
        return
    
    print("editing on line", index, __init__, ":", 'del ' + func)
    lines = file.readlines()
    lines.insert(index, 'del ' + func)
    file.writelines(lines)
    return run(package, debug=debug)
    
@singledispatch
def process(package, debug=False):
    module = import_module(package)
#     https://www.geeksforgeeks.org/try-except-vs-if-in-python/
# We often hear that python always encourages EAFP(
# "It's easier to ask for forgiveness than permission") 
# style over LBYL ( "Look before you leap " ) style used in most of the languages like C.
    try: 
        file = module.__file__
        if debug:
            print(file)
            
        state, lapse, latex = prove_with_timing(module, debug=debug)
    except AttributeError as e:
        lapse = 0
        latex = None
        
        if module is not None:
            print(module, 'from', module)
            print(e)
            if m := re.fullmatch("module '([\w\.]+)' has no attribute '(\w+)'", str(e)):
                print('importing errors found in', package)
    
                _package, module = re.match('(.*)\.(\w+)', package).groups()
                _package = 'axiom.' + _package
                if create_module(_package, module):
                    print("file =", file, type(file))
                    if m[2] == 'prove' and basename(file) == '__init__.py':
                        pyFile = re.sub(r"[\\/]__init__\.py$", '.py', file)
                        print("pyFile =", pyFile)
                        if exists(pyFile):
                            print('try to update', file)
                            file = Text(file)
                            file.writelines([*Text(pyFile)] + [*file])
                            removeFile(pyFile)
            elif re.match("type object '[\w.]+' has no attribute 'prove'", str(e)):
                lapse = 0
                latex = None
                tackle_type_error(package, debug)

        state = RetCode.failed
        file = project_directory() + sep + package.replace('.', sep) + '.py'        
    except TypeError:
        lapse = 0
        latex = None
        tackle_type_error(package, debug)
        state = RetCode.failed
        file = project_directory() + sep + package.replace('.', sep) + '.py'        
        
    return package, file, state, lapse, latex


@process.register(list) 
def _(packages, debug=False):
    return [process(package, debug=debug) for package in packages]


start = time.time()

user = basename(dirname(realpath(__file__)))
assert user, 'user should not be empty!'

try:
    from std import MySQL

    def select_axiom_lapse_from_axiom(self):
        import mysql.connector
        try:
            return {axiom: lapse for axiom, lapse in self.query("select axiom, lapse from axiom where user='%s'" % user)}
        except mysql.connector.errors.ProgrammingError as err:
            print(err.msg)
            m = re.compile("Table '(\w+)\.([\w_]+)' doesn't exist").search(err.msg)
            assert m
            assert m[1] == 'axiom'
            assert m[2] == 'axiom'
            sql = '''\
    CREATE TABLE `axiom` (
      `user` varchar(32) NOT NULL,
      `axiom` varchar(256) NOT NULL,  
      `state` enum('proved', 'failed', 'plausible', 'unproved', 'unprovable', 'slow') NOT NULL,
      `lapse` double default NULL,  
      `latex` text NOT NULL,
      PRIMARY KEY (`user`, `axiom`) 
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
            sql = '''\
    CREATE TABLE `hierarchy` (
      `user` varchar(32) NOT NULL,
      `caller` varchar(256) NOT NULL,
      `callee` varchar(256) NOT NULL,
      `count` int DEFAULT '0',
      PRIMARY KEY (`user`,`caller`,`callee`)
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
                      
#ai = accent insensitivity; ci = case insensitivity
#as = accent sensitivity  ; cs = case sensitivity 
            sql = '''\
    CREATE TABLE `hint` (
      `prefix` varchar(36) NOT NULL,
      `phrase` varchar(36) NOT NULL,
      `usage` int DEFAULT '1',
      PRIMARY KEY (`prefix`,`phrase`)
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE utf8mb4_0900_as_cs
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
                  
            sql = '''\
    CREATE TABLE `suggest` (
      `user` varchar(32) NOT NULL,
      `prefix` varchar(256) NOT NULL,
      `phrase` varchar(32) NOT NULL,
      `usage` int DEFAULT '1',
      PRIMARY KEY (`user`,`prefix`,`phrase`)
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
                    
            sql = '''\
    CREATE TABLE `login` (
      `user` varchar(32) NOT NULL,
      `password` varchar(32) NOT NULL,
      `email` varchar(128) NOT NULL,
      `port` int DEFAULT '0',
      `visibility` enum('public','private','protected') NOT NULL,
      PRIMARY KEY (`user`)
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
            
            sql = "insert into login values('sympy', '123456', 'chenlizhibeing@126.com', 'protected')"
            self.execute(sql)
            
            sql = '''\
    CREATE TABLE `debug` (  
      `symbol` varchar(64) NOT NULL,
      `script` text NOT NULL,
      `latex` text NOT NULL,
      PRIMARY KEY (`symbol`)
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
            
            sql = '''\
    CREATE TABLE `function` (
      `user` varchar(32) NOT NULL,
      `caller` varchar(256) NOT NULL,
      `callee` varchar(256) NOT NULL,
      `func` varchar(64) NOT NULL,
      PRIMARY KEY (`user`,`caller`,`callee`)
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci
    PARTITION BY KEY () 
    PARTITIONS 8
    '''
            self.execute(sql)
            
            sql = '''\
    CREATE TABLE `breakpoint` (
      `user` varchar(32) NOT NULL,
      `module` varchar(256) NOT NULL,  
      `line` int NOT NULL,
      PRIMARY KEY (`user`, `module`, `line`) 
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8
    '''
            self.execute(sql)
            
        except Exception as e:
            print(type(e), e)
            
        return {}

    MySQL.instance.select_axiom_lapse_from_axiom = lambda : select_axiom_lapse_from_axiom(MySQL.instance)
    MySQL.instance.url_address = lambda package: f"http://localhost/{user}/index.php?module={package}"
    
except Exception as e:
    from util import javaScript as MySQL


def select_axiom_by_state_not(user, state):
    yield from MySQL.instance.query(f"select axiom, state from axiom where user = '{user}' and state != '{state}'")


def select_count(user, state=None):
    sql = f"select count(*) from axiom where user = '{user}'"
    if state:
        sql += f" and state = '{state}'"

    [[count]] = MySQL.instance.query(sql)
    return count


def prove(**kwargs):
    def generator(): 
        rootdir = axiom_directory()
#         rootdir += r'\algebra\imply\le\abs'
        for name in os.listdir(rootdir):
            path = join(rootdir, name)
            
            if isdir(path):
                if name != '__pycache__':
                    yield from readFolder(path)

    taskSet = {*generator()}
    
    # taskSet = {*[*taskSet][:100]}

    tasks = MySQL.instance.select_axiom_lapse_from_axiom()
    deleteSet = tasks.keys() - taskSet
    if len(deleteSet) > 1:
        MySQL.instance.execute("delete from axiom where user='%s' and axiom in %s" % (user, tuple(deleteSet)))
    elif len(deleteSet) == 1:
        deleteAxiom, *_ = deleteSet
        MySQL.instance.execute("delete from axiom where user='%s' and axiom = '%s'" % (user, deleteAxiom))
    for key in deleteSet:
        del tasks[key]
    
    newTasks = taskSet - tasks.keys()
    if newTasks:
        for i, module in enumerate(newTasks):
            tasks[module] = random.random()

    packages = tuple([] for _ in range(cpu_count()))
    timings = [0 for _ in range(cpu_count())]
    
    total_timing = sum(timing for task, timing in tasks.items())
    
    average_timing = total_timing / len(packages)
    print('total_timing =', total_timing)
    print('average_timing =', average_timing)
    
    tasks = [*tasks.items()]
    tasks.sort(key=lambda pair: pair[1], reverse=True)
    
    pq = PriorityQueue()
    for i, t in enumerate(timings):
        pq.put((t, i))

    for task, timing in tasks:
        t, i = pq.get()
        packages[i].append(task)
        timings[i] += timing
        pq.put((timings[i], i))
        
    for proc, timing in zip(packages, timings):
        print('timing =', timing)
        print('python run.py ' + ' '.join(proc))
        
    print('total timing =', sum(timings))
    
    data = []
    
    for array in process(packages, **kwargs):
        data += post_process(array)

    MySQL.instance.load_data('axiom', data, replace=True, truncate=True)

    print('in all %d axioms' % Globals.count)
    print_summary()

    
def print_summary():
    if Globals.plausible:
        print('plausible:')
        for p in Globals.plausible:
            for p in p:
                print(p)
            print()
            
    if Globals.failed:
        print('failed:')
        for p in Globals.failed:
            for p in p:
                print(p)
            print()

    timing = time.time() - start
    print('seconds costed =', timing)
    print('minutes costed =', timing / 60)    
    print('total plausible =', len(Globals.plausible))
    print('total failed    =', len(Globals.failed))

        
def post_process(result):
    data = []
    for package, file, state, lapse, latex in result:
        if latex is None:
            print(package)
            print(file)
            latex = ''
            assert state is RetCode.failed
            
        if state is RetCode.slow:
            print(f"{package} is not added to the data since it is not modified!")
        else:
            data.append((user, package, state, lapse, latex))
            
        if state is RetCode.plausible:
            Globals.plausible.append((file, MySQL.instance.url_address(package)))
        elif state is RetCode.failed:
            Globals.failed.append((file, MySQL.instance.url_address(package)))
        else:
            continue
        
    return data

def process_debug(packages):
    return process(packages, debug=True)


@process.register(tuple) 
def _(items, debug=False, parallel=True):  # @DuplicatedSignature
    proc = process_debug if debug else process
    if parallel:        
        return batch_map(proc, items, processes=cpu_count()) 
    else:
        return map(proc, items)

       
def listdir(rootdir, sufix='.php'):
    for name in os.listdir(rootdir):
        path = join(rootdir, name)

#         if path.endswith(sufix):
#             yield path
        if isdir(path):
            yield from listdir_recursive(path, sufix)


def listdir_recursive(rootdir, sufix='.php'):
    for name in os.listdir(rootdir):
        path = join(rootdir, name)

        if path.endswith(sufix):
            yield path
        elif isdir(path):
            yield from listdir_recursive(path, sufix)


def removeFile(path):
    try:
        print(f'removing {path}')
        os.remove(path)
    except PermissionError as e:
        print(e)

    
def args_kwargs(argv):
    args = []
    kwargs = {}
    for arg in argv:
        arr = arg.split('=')
        if len(arr) == 2:
            key, value = arr
            kwargs[key] = eval(value)
        else:
            args.append(arg)
    return args, kwargs

def retry(package):
    from util.search import module_to_py
    file = module_to_py(package)
    __init__ = dirname(file) + '/__init__.py'
    bn = basename(file)[:-3]
    for line in Text(__init__):
        if re.match('from \. import %s' % bn, line):
            return post_process_returns(run(package, debug=False))

    return RetCode.failed, None, None
    
def post_process_returns(returns):
    for line in returns:
        m = re.match(r"seconds costed = (\d+\.\d+)", line)
        if m:
            lapse = float(m[1])
            continue
            
        m = re.match(r"exit_code = (\S+)", line)
        if m:
            state = int(m[1])
            if state > 0:
                state = RetCode.proved
            elif state < 0:
                state = RetCode.failed
            else:
                state = RetCode.plausible
            continue
        
        m = re.match(r"latex results are saved into: (\S+)", line)
        if m:
            sql = m[1]
            text = Text(sql)
            for line in text:
                m = re.match('update axiom set state = "\w+", lapse = \S+, latex = ("[\s\S]+") where user = "\w+" and axiom = "\S+"', line)
                if m:
                    latex = eval(m[1])

            text.close()
            os.unlink(sql)
            continue
        
        print(line.rstrip())

    return state, lapse, latex


def run_with_module(*modules, debug=True):

    def generator():
        for package in modules:
            package = package.replace('/', '.').replace('\\', '.')
            module = import_module(package)
            
            if module is None:
                file = project_directory() + '/' + package.replace('.', '/') + '.py'
                args = RetCode.failed, None, None
            else: 
                try:
                    args = prove_with_timing(module, debug=debug, slow=True)
                    file = module.__file__
                except AttributeError as e:
                    if re.match("'function' object has no attribute 'prove'", str(e)):
                        args = retry(package)

                    elif m := re.match("module '([\w.]+)' has no attribute 'prove'", str(e)):
                        if m[1].startswith('sympy.'):
                            args = post_process_returns(tackle_type_error(package, False))
                        else:
                            args = retry(package)

                    elif re.match("type object '[\w.]+' has no attribute 'prove'", str(e)):
                        args = post_process_returns(tackle_type_error(package, False))

                    else: 
                        continue
                
            yield package, file, *args

    for args in post_process(generator()):
        print('\v'.join((str(arg) for arg in args)).encode(encoding='utf8'))
    
    print_summary()
    
    if Globals.plausible: 
        exit_code = 0
    elif Globals.failed:
        exit_code = -1
    else:
        exit_code = 1
        
    print('exit_code =', exit_code)
    exit(exit_code)


if __name__ == '__main__':
    is_http = 'HTTP_HOST' in os.environ
    if is_http:
        print("Content-type:text/html\n")        
        QUERY_STRING = os.environ['QUERY_STRING']
#         print("QUERY_STRING =", QUERY_STRING, "<br>")
        
        if not QUERY_STRING:
            kwargs = {}            
        else:
            kwargs = {key: value for key, value in map(lambda s: s.split('='), QUERY_STRING.split('&'))}
        
#         print("kwargs =", kwargs, "<br>")        
        args = ''
        
    else: 
        args, kwargs = args_kwargs(sys.argv[1:])
        
    debug = kwargs.pop('debug', False)
    parallel = kwargs.pop('parallel', not sys.gettrace())
    if not args:
        if kwargs:
            for key, value in kwargs.items():
                if key == 'module':
                    run_with_module(value, debug=debug)                    
                elif key == 'hierarchy':
                    from util.hierarchy import insert_into_hierarchy
                    insert_into_hierarchy()
        else:
            if is_http:
                print('''
<style type="text/css">
body {
    background-color: rgb(199, 237, 204);
    margin-left: 1.5em;
}
</style>

<script>
var ret = setInterval(()=>{
    var textarea = document.querySelector('textarea');
    if (textarea){
        console.log("textarea.scrollTop = textarea.scrollHeight;");
        textarea.scrollTop = textarea.scrollHeight;
    }
},
1000);
</script>

<textarea
readonly=true
spellcheck=false
style="height:100%; width:100%; overflow:auto; word-break:break-all; background-color:rgb(199, 237, 204);">
''')
                prove(debug=debug, parallel=parallel)
                print(r'''</textarea>
<div></div>
<script>
var textarea = document.querySelector('textarea');
var lines = textarea.value;
lines = lines.split(/\n/);
var div = document.querySelector('div');
for (let line of lines){
    if (line.endsWith('.py'))
        continue;
        
    var el;
    if (line.startsWith('http')){
        el = document.createElement('a');
        el.href = line;
        line = line.match(/module=(\S+)/)[1];
        el.innerText = line;
    }
    else{
        el = document.createElement('p');
        el.innerText = line;
    }
    
    div.appendChild(el);
}
textarea.remove();
el.scrollIntoView();
clearInterval(ret);
</script>''')
            else:
                prove(debug=debug, parallel=parallel)
            
    else: 
        run_with_module(*args)


# python -c "exec(open('./util/function.py').read())"
# python -c "exec(open('./util/hierarchy.py').read())"
# python -c "exec(open('./util/hint.py').read())"
# python -c "exec(open('./util/suggest.py').read())"