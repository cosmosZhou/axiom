from util import *


@apply
def apply(self, i=None):
    [*args] = self.of(And)
    if i is None:
        for i, eq in enumerate(args):
            if eq.is_Or:
                break
        else:
            return
    else:
        eq = args[i]

    del args[i]
    this = self.func(*args)
    return Or(*((arg & this).simplify() for arg in eq.of(Or)))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    # Eq << Eq[-2].this.lhs.apply(Algebra.et.then.ou, simplify=False)
    Eq << Eq[-1].this.rhs.apply(Algebra.Or.to.And.collect, cond=f(x) < g(y), simplify=False)




if __name__ == '__main__':
    run()

# created on 2018-01-21
del collect
# updated on 2023-05-10


from . import collect
