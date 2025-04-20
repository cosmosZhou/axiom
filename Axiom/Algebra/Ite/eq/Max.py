from util import *


@apply
def apply(self):
    (s, et), (S[-oo], S[True]) = self.of(Piecewise)
    eqs = et.of(Or)

    return Equal(self, Max(*(Piecewise((s, eq), (-oo, True)) for eq in eqs)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    s = Function(real=True)
    x = Symbol(real=True)
    f, g = Function(real=True, shape=())
    Eq << apply(Piecewise((s(x), (f(x) > 0) | (g(x) > 0)), (-oo, True)))

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[0], cond=Eq[0].find(Greater))

    Eq <<= Logic.Imp.given.Imp.subs.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subs.Bool.apply(Eq[-1], invert=True)

    Eq << Logic.Imp.given.Cond.apply(Eq[-1])

    Eq << Algebra.Eq_Max.given.Le.apply(Eq[-1])

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-04-23
# updated on 2023-04-29
