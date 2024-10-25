from util import *


@apply
def apply(self, *, simplify=True):
    ecs, *limits_d = self.of(Derivative[Piecewise])

    args = []
    for expr, cond in ecs:
        expr = Derivative(expr, *limits_d)

        if simplify:
            expr = expr.doit()

        args.append((expr, cond))


    return Equal(self, Piecewise(*args))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](Piecewise((f(x), Element(x, A)), (g(x), True))))

    Eq << algebra.cond_piece.of.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.cond.cond.of.et.subs)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.of.et.subs, invert=True)





if __name__ == '__main__':
    run()
# created on 2023-03-31
# updated on 2023-05-20
