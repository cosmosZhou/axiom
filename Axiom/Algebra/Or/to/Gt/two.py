from util import *


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)
    assert len(or_eqs) == 2
    from Axiom.Sets.Or.to.In.Piece.two import expr_cond_pair
    return Greater(Piecewise(*expr_cond_pair(Greater, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, p = Symbol(real=True, given=True)
    A = Symbol(etype=dtype.real, given=True)
    f, g = Function(real=True)
    Eq << apply(Greater(f(x), p) & Element(x, A) | Greater(g(x), p) & NotElement(x, A), wrt=p)

    Eq << Eq[1].apply(Algebra.Cond.of.And.Or, cond=Element(x, A))

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Algebra.Cond.Cond.to.Cond.subs, invert=True, swap=True, ret=1), Eq[-1].apply(Algebra.Cond.Cond.to.Cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.And.to.Or.apply(Eq[-2])


if __name__ == '__main__':
    run()

# created on 2020-01-12