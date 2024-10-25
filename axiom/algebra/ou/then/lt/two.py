from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.then.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)
    assert len(or_eqs) == 2
    return Less(Piecewise(*expr_cond_pair(Less, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import algebra

    x, p = Symbol(real=True, given=True)
    A = Symbol(etype=dtype.real, given=True)
    f, g = Function(real=True)
    Eq << apply(Less(f(x), p) & Element(x, A) | Less(g(x), p) & NotElement(x, A), wrt=p)

    Eq << Eq[1].apply(algebra.cond.of.et.ou, cond=Element(x, A))

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebra.cond.cond.then.cond.subs, invert=True, swap=True, ret=1), Eq[-1].apply(algebra.cond.cond.then.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << algebra.et.then.ou.apply(Eq[-1])

    Eq << algebra.et.then.ou.apply(Eq[-2])


if __name__ == '__main__':
    run()

# created on 2019-08-05
