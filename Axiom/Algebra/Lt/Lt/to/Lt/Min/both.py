from util import *



@apply
def apply(x_less_than_y, a_less_than_b):
    x, y = x_less_than_y.of(Less)
    a, b = a_less_than_b.of(Less)
    return Less(Min(x, a), Min(y, b))


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y, a, b = Symbol(real=True)


    Eq << apply(x < y, a < b)

    Eq << LessEqual(Min(x, a), x, plausible=True)

    Eq << Algebra.Le.Lt.to.Lt.trans.apply(Eq[-1], Eq[0])

    Eq << LessEqual(Min(x, a), a, plausible=True)

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[1], Eq[-1])

    Eq << Algebra.Lt.Lt.to.Lt.Min.apply(Eq[-1], Eq[-3])

if __name__ == '__main__':
    run()
# created on 2019-05-12
