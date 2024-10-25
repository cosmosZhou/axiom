from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, j), (S[j], n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1

    return GreaterEqual(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq.case2, Eq.case1 = algebra.cond.of.et.infer.split.apply(Eq[-1], cond=n >= 2)

    Eq << Eq.case1.this.lhs.apply(algebra.lt.to.eq.squeeze)

    Eq << Eq[-1].this.apply(algebra.infer.subs)

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << algebra.infer.of.cond.apply(Eq[-1])

    Eq << algebra.all.then.cond.subs.apply(Eq[0], i, 1)

    _n = Symbol('n', domain=Range(2, oo))

    Eq << Eq[0].subs(n, _n)

    Eq << discrete.all_ge.then.gt.K.apply(Eq[-1])

    Eq << algebra.cond.then.all.apply(Eq[-1], _n)

    Eq << Eq[-1].this.expr.apply(algebra.gt.then.ge.relax)

    Eq << algebra.infer.of.all.apply(Eq.case2)


if __name__ == '__main__':
    run()

# created on 2020-09-16
