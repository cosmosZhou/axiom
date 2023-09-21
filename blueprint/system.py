from flask.blueprints import Blueprint
import std
from flask.globals import request

system = Blueprint('system', __name__, static_folder='../static')


@system.route('/favicon.ico')
def favicon():
    return system.send_static_file('favicon.ico')

@system.route('/kill', methods=['GET'])
def kill():
    import signal
    import os
    os.kill(os.getpid(), signal.SIGILL)
    return std.json_encode({'text': 'kill myself'})

import ast
from sympy import *

@system.route('/eval', methods=['POST', 'GET'])
def evaluate():
    data = {**request.args} | {**request.form}
    if not data:
        data = {**request.json}
        
    try:
        python = data['python']
        lineno = ast.parse(python).body[-1].lineno - 1
        lines = python.split('\n')
        given, imply = lines[:lineno], lines[lineno:]
        given.insert(0, 'from sympy import *')
        given = '\n'.join(Symbol.compile_definition_statement(given) for given in given)
        imply = '\n'.join(imply)
        __locals__ = {}
        exec(given, __locals__)
        obj = eval(imply, __locals__)
        latex = sympify(obj).latex
        return std.json_encode(dict(latex=latex))
    except Exception as e:
        from std.error import Cout
        print(e, file=Cout)
        import traceback
        traceback.print_exc(file=Cout)
        return std.json_encode(dict(error=str(Cout), path='\n'.join(sys.path), version=sys.version))


@system.route('/system/user')
def system_user():
    from util.utility import user
    return user
