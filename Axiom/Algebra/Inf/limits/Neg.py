from util import *


@apply
def apply(self):
    expr, (x, *ab) = self.of(Inf)
    if len(ab) == 2:
        a, b = ab
        if x.is_integer:
            limit = (x, 1 - b, 1 - a)
        else:
            limit = (x, -b, -a)
    else:
        domain, = ab
        limit = (x, -domain)

    return Equal(self, Inf(expr._subs(x, -x), limit))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)))

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition.reversed

    Eq << Algebra.Eq.to.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.to.All.Any.Lt.apply(Eq[-2]), Algebra.GeInf.to.All.Ge.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1]).reversed

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2]), Algebra.GeInf.of.All.Ge.apply(Eq[-1])
    Eq <<= Eq[-2].this.expr.apply(Algebra.Any.limits.Neg), Eq[-1].this.apply(Algebra.All.limits.Neg)


if __name__ == '__main__':
    run()
# created on 2019-10-03
