from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr >= Max)
    if index is None:
        eqs = [x >= arg for arg in args]
    else:
        first = args[:index]
        second = args[index:]
        eqs = x >= Max(*first), x >= Max(*second)

    return And(*eqs)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Max(y, z))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ge_Max.to.And.Ge)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge.Ge.to.Ge.Max)




if __name__ == '__main__':
    run()
# created on 2022-01-01
