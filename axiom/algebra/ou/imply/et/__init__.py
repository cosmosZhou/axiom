from util import *


@apply
def apply(self, index=-1):
    [*args] = self.of(Or)
    for i, eq in enumerate(args):
        if isinstance(eq, And):
            break
    else:
        return

    del args[i]
    this = self.func(*args)
    args = eq.args
    if index is None:
        return tuple((eq | this).simplify() for eq in args)
        
    lhs = And(*args[:index])
    rhs = And(*args[index:])

    return (lhs | this).simplify(), (rhs | this).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y))))

    Eq << Eq[0].this.args[1].apply(algebra.et.imply.cond, index=1)

    Eq << Eq[0].this.args[1].apply(algebra.et.imply.cond, index=0)

    


if __name__ == '__main__':
    run()

from . import collect
from . import infer
# created on 2019-04-29
# updated on 2022-01-28
