from util import *


@apply
def apply(given, index=-1):
    from axiom.algebra.all.imply.all.limits.split import split
    return split(given, index)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True)

    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True)

    Eq << apply(All[x[:n + 1]:CartesianSpace(Interval(a, b), n + 1)](f(x[:n + 1]) > 0), index=n)

    Eq << algebra.all.imply.all.limits.merge.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-12-10
