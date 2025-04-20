from util import *


@apply
def apply(self, *, simplify=True):
    [*args] = self.of(Mul)
    for i, rhs in enumerate(args):
        if rhs.is_Piecewise:
            break
    else :
        return

    del args[i]
    delta = Mul(*args, evaluate=False)

    if not delta.is_One:
        rhs = Piecewise(*((e * delta, c) for e, c in rhs.args))

    if simplify:
        rhs = rhs.simplify()
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x, y = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Piecewise((g(x), x > 0), (h(x), True)) * y)

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Algebra.Cond.Cond.given.And.subs)

    Eq << Eq[-1].this.args[1].apply(Algebra.Cond.Cond.given.And.subs, invert=True)


if __name__ == '__main__':
    run()
# created on 2022-01-23


# updated on 2023-05-20
