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

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.infer_et.imply.infer.et.subs.bool, index=1)

    Eq << Eq[-1].this.rhs.apply(algebra.infer_et.given.infer.et.subs.bool, index=1)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-05-17
