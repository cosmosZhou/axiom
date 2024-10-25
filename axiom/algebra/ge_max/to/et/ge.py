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
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Max(y, z))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge_max.then.et.ge)

    Eq << Eq[-1].this.rhs.apply(algebra.ge.ge.then.ge.max)




if __name__ == '__main__':
    run()
# created on 2022-01-01
