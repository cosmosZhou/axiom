from util import *


@apply
def apply(self):
    (s, et), (S[oo], S[True]) = self.of(Piecewise)
    eqs = et.of(Or)

    return Equal(self, Min(*(Piecewise((s, eq), (oo, True)) for eq in eqs)))


@prove
def prove(Eq):
    from axiom import algebra

    s = Function(real=True)
    x = Symbol(real=True)
    f, g = Function(real=True, shape=())
    Eq << apply(Piecewise((s(x), (f(x) > 0) | (g(x) > 0)), (oo, True)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Eq[0].find(Greater))

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.rhs.apply(algebra.eq_min.given.le)

    Eq << algebra.infer.given.cond.apply(Eq[-1])

    Eq << algebra.cond_piece.given.ou.apply(Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-23
# updated on 2023-04-29
