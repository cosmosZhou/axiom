from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sum)
    return self <= Sum(Abs(expr), *limits)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:n](f(k)))

    Eq << algebra.imply.le.abs.apply(f(k))

    Eq << algebra.le.imply.le.sum.apply(Eq[-1], (k, 0, n))


if __name__ == '__main__':
    run()
# created on 2023-04-15
