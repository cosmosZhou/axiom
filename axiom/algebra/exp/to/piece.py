from util import *


@apply
def apply(self):
    ecs = self.of(Exp[Piecewise])
    return Equal(self, Piecewise(*((exp(e), c) for e, c in ecs)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    A = Symbol(etype=dtype.real)
    x, t = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(exp(Piecewise((g(x), Element(x, A)),(h(x), True))))

    Eq << algebra.cond_piece.of.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.cond.cond.of.et.subs)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.of.et.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2019-05-08
# updated on 2023-05-14
