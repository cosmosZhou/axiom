from util import *


@apply
def apply(self, i=None):
    [*args] = self.of(And)
    if i is None:
        for i, eq in enumerate(args):
            if eq.is_Or:
                break
        else :
            return
    else :
        eq = args[i]

    del args[i]
    this = self.func(*args)
    return Or(*((arg & this).simplify() for arg in eq.of(Or)))


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.et.apply(Eq[0])

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[-2], Eq[-3], invert=True)

    Eq <<= Eq[-1] & Eq[-2]





if __name__ == '__main__':
    run()

del collect
from . import collect
# created on 2018-01-06
# updated on 2023-05-13
