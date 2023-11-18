from util import *


@apply
def apply(given):
    return piecewise_to_ou(given)


def piecewise_to_ou(given):
    piecewise, sym = given.args
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise

    (e0, c0), (e1, _) = piecewise.of(Piecewise)

    univeralSet = S.true

    condition = c0 & univeralSet

    invert = condition.invert()
    univeralSet &= invert

    cond0 = condition & given.func(sym, e0).simplify()

    cond1 = univeralSet & given.func(sym, e1).simplify()

    return Or(cond0, cond1)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A = Symbol(etype=dtype.real[k], given=True)
    f, g = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), True))))

    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=Element(x, A))

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq <<= algebra.ou.imply.ou.invert.apply(Eq[-2], pivot=1), algebra.ou.imply.ou.invert.apply(Eq[-1], pivot=1)

    Eq <<= Eq[-2].this.find(And).apply(algebra.cond.cond.imply.cond.subs, invert=True, swap=True, ret=1), Eq[-1].this.find(And).apply(algebra.cond.cond.imply.cond.subs, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    
    


if __name__ == '__main__':
    run()

# created on 2018-01-07
# updated on 2023-05-19
