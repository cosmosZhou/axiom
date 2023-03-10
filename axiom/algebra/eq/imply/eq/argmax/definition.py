from util import *


@apply
def apply(given):
    x0, argmax_fx = given.of(Equal)
    function, limit = argmax_fx.of(ArgMax)
    x = limit[0]
    fx0 = function._subs(x, x0)
    return Equal(fx0, Maxima(function, limit))


@prove(provable=False)
def prove(Eq):
    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMax[x](f(x))))


if __name__ == '__main__':
    run()
# created on 2019-04-12
