from util import *


@apply
def apply(all_le):
    (lhs, rhs), *limits = all_le.of(All[Greater])
    lhs = Lamda(lhs, *limits).simplify()
    rhs = Lamda(rhs, *limits).simplify()
    return lhs > rhs


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n](x[i] > y[i]))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all_gt.then.gt.lamda)

    Eq << Eq[-1].this.lhs.apply(algebra.all_gt.of.gt.lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
