from util import *


@apply
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, Or):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            return Or(*((arg & this).simplify() for arg in eq.args))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << Algebra.Or.to.And.collect.apply(Eq[1])
    Eq << Algebra.And.of.And.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-05-04
del collect


from . import collect