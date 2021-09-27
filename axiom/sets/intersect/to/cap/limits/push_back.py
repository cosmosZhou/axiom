from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.push_back import absorb
    return Equal(self, absorb(Cap, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets
    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(0, n + 1))
    f = Function(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:i:n](f(k)), f(n), evaluate=False))

    Eq << Eq[-1].this.rhs.apply(sets.cap.to.intersect.split, {n})


if __name__ == '__main__':
    run()
