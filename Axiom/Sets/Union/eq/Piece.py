from util import *


@apply
def apply(self):
    [*args] = self.of(Union)
    for i, piecewise in enumerate(args):
        if piecewise.is_Piecewise:
            del args[i]
            break
    else:
        return

    s = Union(*args)

    ecs = ((e | s, c) for e, c in piecewise.args)
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(integer=True)
    f, g, h, t = Function(etype=dtype.real)
    Eq << apply(Union(Piecewise((f(x), x > 0), (g(x), True)), h(x), t(x), evaluate=False))

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Algebra.Cond.Cond.of.And.subs)

    Eq << Eq[-1].this.args[1].apply(Algebra.Cond.Cond.of.And.subs, invert=True)





if __name__ == '__main__':
    run()

# created on 2021-01-24
# updated on 2023-05-09
