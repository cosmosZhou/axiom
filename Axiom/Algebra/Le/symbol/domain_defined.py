from util import *


@apply
def apply(x):
    domain = x.domain
    return LessEqual(*domain.of(Interval))


@prove
def prove(Eq):
    from Axiom import Set
    a, b = Symbol(real=True)
    domain=Interval(a, b)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << Element(x, domain, plausible=True)

    Eq << Set.Ne_EmptySet.of.Mem.apply(Eq[-1])
    Eq << Set.Le.of.Icc_Ne_EmptySet.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-24
