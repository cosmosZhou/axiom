from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, j), (S[j], n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1
    assert n >= 2
    return Greater(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq << Eq[-1].this.find(K).defun()

    Eq << algebra.all.then.et.all.split.apply(Eq[0], cond={n})

    Eq << Eq[-1].this.expr.apply(algebra.ge.then.gt_zero)

    Eq << discrete.all_gt_zero.then.gt_zero.K.apply(Eq[-1])

    Eq << algebra.gt_zero.ge.then.ge.mul.apply(Eq[-1], Eq[-4])

    Eq << algebra.all.then.et.all.split.apply(Eq[-3], cond={n - 1})

    Eq << discrete.all_gt_zero.then.gt_zero.K.apply(Eq[-1])

    Eq << algebra.gt.ge.then.gt.add.apply(Eq[-1], Eq[-4])





if __name__ == '__main__':
    run()

# created on 2020-09-16
# updated on 2023-10-22
