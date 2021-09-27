from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.push_front import absorb
    return Equal(self, absorb(Cap, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets

    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(0, n))
    f = Function(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:1 + i:n](f(k)), f(i), evaluate=False))

    Eq << Eq[-1].this.rhs.apply(sets.cap.to.intersect.split, {i})


if __name__ == '__main__':
    run()
