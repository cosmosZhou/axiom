from util import *


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)

    assert len(or_eqs) == 2
    from Axiom.Sets.Or.to.In.Piece.two import expr_cond_pair
    return Supset(Piecewise(*expr_cond_pair(Supset, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, S = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(etype=dtype.real[k])
    Eq << apply(Supset(f(x), S) & Element(x, A) | Supset(g(x), S) & NotElement(x, A), wrt=S)

    Eq << Eq[1].apply(Algebra.Cond.of.And.Or, cond=Element(x, A))

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Algebra.Cond.Cond.to.Cond.subs, invert=True, swap=True, ret=1), Eq[-1].apply(Algebra.Cond.Cond.to.Cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Algebra.And.to.Or.apply(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-06-14