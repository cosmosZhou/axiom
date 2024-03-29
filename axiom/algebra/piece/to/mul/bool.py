from util import *


@apply
def apply(self):
    (expr, cond), (S[0], S[True]) = self.of(Piecewise)
    return Equal(self, expr * Bool(cond))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    g = Function(shape=(), real=True)
    p = Function(bool=True)
    Eq << apply(Piecewise((g(x), p(x)), (0, True)))

    Eq << Eq[-1].this.lhs.apply(algebra.piece.to.mul)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.bool)


if __name__ == '__main__':
    run()
# created on 2023-06-18
