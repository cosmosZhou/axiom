from util import *


@apply
def apply(given, index=0, invert=False):
    et, f = given.of(Imply)
    eqs = et.of(And)

    eq = eqs[index]

    if invert:
        old = eq.invert()
        new = S.false
    else:
        old = eq
        new = S.true

    return Imply(et, f._subs(old, new))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Imply(Equal(t(x), y) & (f(x) > y), Equal(g(x), Piecewise((f(x), (f(x) > y)), (t(x), True)))))

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[0], 0)


    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Cond.to.Cond.subs)



if __name__ == '__main__':
    run()
# created on 2023-04-25
