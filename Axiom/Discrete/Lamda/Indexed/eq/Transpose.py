from util import *


@apply
def apply(self):
    expr, *limits, (i, a, b) = self.of(Lamda)
    expr = Lamda[i:a:b](expr).simplify()
    expr = Lamda(expr, *limits).simplify()

    if len(limits) > 1:
        axis = [(-axis - 1,) for axis in range(len(limits))]
    else:
        axis = ()

    return Equal(self, Transpose(expr, *axis))


@prove
def prove(Eq):
    from Axiom import Algebra

    n, d = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n, n * 2, n), real=True)
    i, j, t = Symbol(integer=True)
    Eq << apply(Lamda[j:n, i:n](x[j, i + d, t]))

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2022-03-16
# updated on 2022-03-17
