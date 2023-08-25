from util import *


@apply
def apply(self):
    function, (x, space) = self.of(Sum)
    domain, n = space.of(CartesianSpace)

    x, (start, stop) = x.of(Sliced)


    assert start + 1 < stop
    assert n == stop - start

    return Equal(self, Sum[x[start]:domain, x[start + 1:stop]:CartesianSpace(domain, n - 1)](function))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]:CartesianSpace(Range(a, b + 1), n - i)](f(x[i:n])))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.find(Element[2]).apply(sets.el_cartesianSpace.to.all.el)

    Eq << Eq[-1].this.rhs.find(All).apply(algebra.all.limits.subs.offset, -i - 1)

    Eq << Eq[-1].this.rhs.find(And).apply(algebra.et.to.all.limits.unshift)

    Eq << Eq[-1].this.lhs.find(Element).apply(sets.el_cartesianSpace.to.all.el)

    Eq << Eq[-1].this.lhs.find(All).apply(algebra.all.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.shift.slice)





if __name__ == '__main__':
    run()

# created on 2020-03-19
# updated on 2023-07-02

from . import cond
