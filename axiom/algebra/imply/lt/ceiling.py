from util import *


@apply
def apply(x):
    return Less(Ceiling(x), x + 1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)

    


if __name__ == '__main__':
    run()

# created on 2018-05-13
# updated on 2018-05-13
