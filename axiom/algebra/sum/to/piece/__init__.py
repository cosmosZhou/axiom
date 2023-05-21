from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sum)
    variables = self.variables

    for _, cond in expr.of(Piecewise):
        assert not cond.has(*variables)

    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in expr.of(Piecewise)]

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    x, y = Symbol(integer=True, given=True)
    A, B, C, D = Symbol(etype=dtype.integer, given=True)
    f, h = Function(real=True)
    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Element(x, A) & Element(y, B)), (h(i, j), True))))

    Eq << algebra.cond_piece.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(algebra.et.given.et.subs.bool, index=slice(1, 3))

    Eq << Eq[-1].this.find(And).apply(algebra.et.given.et.subs.bool, index=1, invert=True)

    Eq << Eq[-1].this.apply(algebra.ou.given.infer, -1)

    
    


if __name__ == '__main__':
    run()


# created on 2020-03-17
# updated on 2023-05-20
from . import pop
from . import unshift
