from util import *


@apply
def apply(given, wrt=None):
    or_eqs = given.of(Or)

    assert len(or_eqs) == 2
    from axiom.sets.ou.then.el.piece.two import expr_cond_pair
    return Subset(Piecewise(*expr_cond_pair(Subset, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, S = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(etype=dtype.real[k])
    Eq << apply(Subset(f(x), S) & Element(x, A) | Subset(g(x), S) & NotElement(x, A), wrt=S)

    Eq << Eq[1].apply(algebra.cond.of.et.ou, cond=Element(x, A))

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebra.cond.cond.then.cond.subs, invert=True, swap=True, ret=1), Eq[-1].apply(algebra.cond.cond.then.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]

    Eq << algebra.et.then.ou.apply(Eq[-1])

    Eq << algebra.et.then.ou.apply(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-06-13
