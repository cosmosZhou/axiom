from util import *


@apply
def apply(given, index=0, invert=False):
    et, f = given.of(Infer)
    eqs = et.of(And)

    eq = eqs[index]

    if invert:
        old = eq.invert()
        new = S.false
    else:
        old = eq
        new = S.true

    return Infer(et, f._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Infer(Equal(t(x), y) & (f(x) > y), Equal(g(x), Piecewise((f(x), (f(x) > y)), (t(x), True)))), index=1)

    Eq << algebra.infer_et.given.infer_et.et.apply(Eq[0], 1)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.cond.given.et.subs)

    


if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-08-26
