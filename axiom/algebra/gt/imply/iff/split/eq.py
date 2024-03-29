from util import *


@apply
def apply(gt, x, y):
    m, n = gt.of(Greater)
    assert m > 0 and n > 0
    assert x.shape[0] >= m
    assert y.shape[0] >= m

    return Equivalent(Equal(x[:m], y[:m]), Equal(x[:n], y[:n]) & Equal(x[n:m], y[n:m]))

@prove
def prove(Eq):
    from axiom import sets

    m, n = Symbol(integer=True, positive=True, given=True)
    x, y = Symbol(real=True, shape=(oo,))
    Eq << apply(m > n, x, y)

    Eq << Element(n, Range(1, m), plausible=True)

    Eq << sets.el_range.given.et.apply(Eq[-1])

    Eq << Eq[-1].reversed

    Eq << sets.el_range.imply.iff.split.eq.apply(Eq[2], x, y)
    


if __name__ == '__main__':
    run()
# created on 2023-03-26
