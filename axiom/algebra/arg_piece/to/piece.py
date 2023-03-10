from util import *


@apply
def apply(self, *, simplify=True):
    ecs = self.of(Arg[Piecewise])
    ecs = [(Arg(e), c) for e, c in ecs]

    return Equal(self, Piecewise(*ecs), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Arg(Piecewise((g(x), x > 0), (h(x), True))))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1, invert=True)


if __name__ == '__main__':
    run()
# created on 2018-11-01
