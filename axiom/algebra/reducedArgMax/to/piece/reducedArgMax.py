from util import *


@apply
def apply(self):
    ecs = []
    for e, c in self.of(ReducedArgMax[Piecewise]):
        ecs.append((ReducedArgMax(e), c))

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra

    m = Symbol(integer=True, positive=True)
    f, g = Function(real=True, shape=(m,))
    x, a, b = Symbol(real=True)
    Eq << apply(ReducedArgMax(Piecewise((f(x), a > b), (g(x), True))))

    Eq << algebra.cond_piece.of.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.cond.cond.of.et.subs)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.of.et.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2021-12-17
# updated on 2023-05-10
