from util import *


@apply
def apply(self):
    function, *limits_d = self.of(Derivative)
    vars = [var for var, _ in limits_d]

    import std
    funcs, coeff = std.array_split(function.of(Mul), lambda arg: arg.has(*vars))
    coeff = Mul(*coeff)
    funcs = Mul(*funcs)
    return Equal(self, coeff * Derivative(funcs, *limits_d))


@prove(proved=False)
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative[x](f(x) * h))


if __name__ == '__main__':
    run()
# created on 2022-01-25
from . import grad
from . import lamda
