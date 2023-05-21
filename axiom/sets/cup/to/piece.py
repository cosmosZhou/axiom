from util import *




@apply
def apply(self):
    fx, *limits = self.of(Cup)
    ecs = []
    variables = self.variables
    for e, c in fx.of(Piecewise):
        assert not c.has(*variables)
        ecs.append((Cup(e, *limits), c))

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(etype=dtype.integer)
    x, y, t = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:A, y:B](Piecewise((f(x, y, t), t > 0), (g(x, y, t), True))))

    Eq << algebra.cond_piece.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1)

    Eq << Eq[-1].this.find(And).apply(algebra.et.given.et.subs.bool, index=1, invert=True)

    
    


if __name__ == '__main__':
    run()

# created on 2018-09-26
# updated on 2023-05-20
