from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return Element(sqrt(x), Reals)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x >= 0)

    y = Symbol(real=True, nonnegative=True)
    Eq << Element(sqrt(y), Reals, plausible=True)

    Eq << Eq[-1].subs(y, x)

    Eq << Eq[-1].this.args[1].simplify()

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[0], Eq[-1], simplify=None)




if __name__ == '__main__':
    run()
# created on 2021-04-11
# updated on 2023-05-09
