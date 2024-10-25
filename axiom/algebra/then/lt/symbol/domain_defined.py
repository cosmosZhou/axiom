from util import *



@apply
def apply(x):
    domain = x.domain
    assert domain.left_open or domain.right_open
    return Less(*domain.of(Interval))


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True)
    domain=Interval(a, b, right_open=True)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << Element(x, domain, plausible=True)

    Eq << sets.el.then.ne_empty.apply(Eq[-1])
    Eq << sets.interval_ne_empty.then.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-25
