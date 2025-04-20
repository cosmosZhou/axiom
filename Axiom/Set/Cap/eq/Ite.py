from util import *




@apply
def apply(self):
    fx, *limits = self.of(Cap)
    ecs = []
    variables = self.variables
    for e, c in fx.of(Piecewise):
        assert not c.has(*variables)
        ecs.append((Cap(e, *limits), c))

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    A, B = Symbol(etype=dtype.integer)
    x, y, t = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:A, y:B](Piecewise((f(x, y, t), t > 0), (g(x, y, t), True))))

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Algebra.Cond.Cond.given.And.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Cond.given.And.subs, invert=True)



if __name__ == '__main__':
    run()

# created on 2021-01-25
# updated on 2023-05-20
