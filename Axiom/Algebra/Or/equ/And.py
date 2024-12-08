from util import *


@apply
def apply(self, i=None):
    [*args] = self.of(Or)
    if i is None:
        for i, eq in enumerate(args):
            if eq.is_And:
                break
        else :
            return
    else :
        eq = args[i]

    del args[i]
    this = self.func(*args)
    return And(*((arg | this).simplify() for arg in eq.of(And)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y))))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Or.to.And)

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.of.And)





if __name__ == '__main__':
    run()

# created on 2020-02-21
# updated on 2023-05-10
