from util import *


@apply
def apply(given):
    from Axiom.Discrete.K.eq.Add.definition import K

    (x, j), (S[j], n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1

    return GreaterEqual(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra
    from Axiom.Discrete.K.eq.Add.definition import K
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq.case2, Eq.case1 = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=n >= 2)

    Eq << Eq.case1.this.lhs.apply(Algebra.Lt.equ.Eq.squeeze)

    Eq << Eq[-1].this.apply(Algebra.Imply.subs)

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << Algebra.All.to.Cond.subs.apply(Eq[0], i, 1)

    _n = Symbol('n', domain=Range(2, oo))

    Eq << Eq[0].subs(n, _n)

    Eq << Discrete.All_Ge.to.Gt.K.apply(Eq[-1])

    Eq << Algebra.Cond.to.All.apply(Eq[-1], _n)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.to.Ge.relax)

    Eq << Algebra.Imply.of.All.apply(Eq.case2)


if __name__ == '__main__':
    run()

# created on 2020-09-16
