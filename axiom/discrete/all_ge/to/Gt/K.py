from util import *


@apply
def apply(given):
    from Axiom.Discrete.K.eq.Add.definition import K
    (x, j), (S[j], n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1
    assert n >= 2
    return Greater(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete
    from Axiom.Discrete.K.eq.Add.definition import K

    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq << Eq[-1].this.find(K).defun()

    Eq << Algebra.All.to.And.All.split.apply(Eq[0], cond={n})

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.to.Gt_0)

    Eq << Discrete.All_Gt_0.to.Gt_0.K.apply(Eq[-1])

    Eq << Algebra.Gt_0.Ge.to.Ge.Mul.apply(Eq[-1], Eq[-4])

    Eq << Algebra.All.to.And.All.split.apply(Eq[-3], cond={n - 1})

    Eq << Discrete.All_Gt_0.to.Gt_0.K.apply(Eq[-1])

    Eq << Algebra.Gt.Ge.to.Gt.Add.apply(Eq[-1], Eq[-4])





if __name__ == '__main__':
    run()

# created on 2020-09-16
# updated on 2023-10-22
