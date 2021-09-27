from util import *


@apply
def apply(x, evaluate=False):
    return GreaterEqual(Ceiling(x), x, evaluate=evaluate)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)

    


if __name__ == '__main__':
    run()

