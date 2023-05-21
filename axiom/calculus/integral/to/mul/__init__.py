from util import *


@apply
def apply(self):
    expr, *limits_d = self.of(Integral)
    vars = [var for var, *ab in limits_d]

    args = expr.of(Mul)
    coeff = []
    funcs = []
    for arg in args:
        if arg.has(*vars):
            funcs.append(arg)
        else:
            coeff.append(arg)
    coeff = Mul(*coeff)
    funcs = Mul(*funcs)
    return Equal(self, coeff * Integral(funcs, *limits_d))


@prove
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x](f(x) * h))

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-03-27


from . import limit
