from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Inf >= Expr)
    return All(fx >= M, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)) >= y)

    z = Symbol(Eq[0].lhs)
    Eq << z.this.definition

    Eq <<= Algebra.Eq_Inf.to.All.Ge.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed)

    Eq <<= Algebra.Cond.All.to.All.And.apply(Eq[-2], Eq[-1], simplify=None)
    Eq <<= Eq[-1].this.expr.apply(Algebra.Ge.Ge.to.Ge.trans)


if __name__ == '__main__':
    run()
# created on 2019-04-06
