from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, x = is_imply_P.of(Given)
    q, y = is_imply_Q.of(Given)

    return Given(p & q, x & y)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Given(x > 0, a > 0), Given(y > 0, b > 0))

    Eq << Algebra.Given.of.Given.split.And.apply(Eq[-1])

    Eq << Eq[-2].this.rhs.apply(Algebra.And.to.Cond, index=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.And.to.Cond, index=1)


if __name__ == '__main__':
    run()
# created on 2018-03-28
