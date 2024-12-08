from util import *


@apply
def apply(self, *, simplify=True):
    piecewise, delta = std.array_split(self.of(Mul), lambda arg: arg.is_Piecewise)

    if not piecewise:
        return

    delta = self.func(*delta, evaluate=False)
    if len(piecewise) == 1:
        result, = piecewise
        if not delta.is_One:
            result = result.func(*((e * delta, c) for e, c in result.args))
    else:
        result = piecewise[0]
        for i in range(1, len(piecewise)):
            result = result.mul(piecewise[i], simplify=simplify)

        if not delta.is_One:
            result = result.func(*((e * delta, c) for e, c in result.args))
    if simplify:
        result = result.simplify()
    return Equal(self, result, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Piecewise((g(x), x > 0), (h(x), True)) * y)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Algebra.Cond.Cond.of.And.subs)

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.Cond.of.And.subs, invert=True)





if __name__ == '__main__':
    run()


# created on 2018-01-20
# updated on 2023-05-20
from . import st
