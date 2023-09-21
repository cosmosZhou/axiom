from util import *


@apply
def apply(self, *, simplify=True):
    ecs = self.of(Floor[Piecewise])
    ecs = [(Floor(e), c) for e, c in ecs]

    return Equal(self, Piecewise(*ecs), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Floor(Piecewise((g(x), x > 0), (h(x), True))))

    Eq << algebra.cond_piece.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.cond.cond.given.et.subs)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.given.et.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2019-05-14
# updated on 2023-05-20
