from util import *


@apply
def apply(self):
    b, ecs = self.of(Expr ** Piecewise)
    return Equal(self, Piecewise(*((b ** e, c) for e, c in ecs)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    A = Symbol(etype=dtype.real)
    x, b = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(b ** Piecewise((g(x), Element(x, A)),(h(x), True)))

    Eq << algebra.cond_piece.of.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.cond.cond.of.et.subs)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.of.et.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2018-04-13
# updated on 2023-05-13
