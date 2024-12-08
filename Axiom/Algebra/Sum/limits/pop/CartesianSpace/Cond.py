from util import *


@apply
def apply(self):
    function, ((x, (start, stop)), cond, (domain, *shape)) = self.of(Sum[Tuple[Sliced, CartesianSpace]])

    n, = shape
    assert start + 1 < stop
    assert n == stop - start

    return Equal(self, Sum[x[start:stop - 1]:cond:CartesianSpace(domain, n - 1), x[stop - 1]:domain](function))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    a, b = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f, g = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]:g(x[i:n]) > 0:CartesianSpace(Range(a, b + 1), n - i)](f(x[i:n])))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.Bool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.Bool)

    Eq << Eq[-1].this.rhs.find(Element[Sliced]).apply(Sets.In_CartesianSpace.equ.All.In)

    Eq << Eq[-1].this.rhs.find(All).apply(Algebra.All.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.find(Element[Sliced]).apply(Sets.In_CartesianSpace.equ.All.In)

    Eq << Eq[-1].this.lhs.find(All).apply(Algebra.All.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.find(All).apply(Algebra.All.equ.And.split, cond={n - 1})




if __name__ == '__main__':
    run()
# created on 2023-08-20
