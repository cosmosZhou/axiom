from util import *


@apply
def apply(x):
    domain = x.domain
    a, b = domain.of(Interval)
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    domain=Interval(a, b)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << algebra.imply.le.symbol.domain_defined.apply(x)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-09-25
