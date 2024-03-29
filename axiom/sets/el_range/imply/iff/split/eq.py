from util import *


@apply
def apply(el, x, y):
    n, (S[1], m) = el.of(Element[Range])
    assert m > 0 and n > 0
    assert x.shape[0] >= m
    assert y.shape[0] >= m

    return Equivalent(Equal(x[:m], y[:m]), Equal(x[:n], y[:n]) & Equal(x[n:m], y[n:m]))

@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True, given=True)
    x, y = Symbol(real=True, shape=(oo,))
    Eq << apply(Element(n, Range(1, m)), x, y)

    k = Symbol(domain=Eq[0].rhs)
    Eq << All[k](Eq[1].cond._subs(n, k), plausible=True)

    Eq << Eq[-1].this.expr.lhs.apply(algebra.eq.to.et.eq.split, Eq[-1].variable)

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], k, n)




if __name__ == '__main__':
    run()
# created on 2023-03-26
