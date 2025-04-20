from util import *



@apply
def apply(x):
    domain = x.domain
    assert domain.left_open or domain.right_open
    return Less(*domain.of(Interval))


@prove
def prove(Eq):
    from Axiom import Set

    a, b = Symbol(real=True)
    domain=Interval(a, b, right_open=True)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << Element(x, domain, plausible=True)

    Eq << Set.Ne_EmptySet.of.Mem.apply(Eq[-1])
    Eq << Set.Lt.of.Icc_Ne_EmptySet.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-25
