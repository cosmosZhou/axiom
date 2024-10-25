from util import *



@apply
def apply(given, wrt=None):
    fn, fn1 = given.of(Infer)
    if wrt is None:
        wrt = fn.wrt
    assert wrt.is_given is None
    return All[wrt:fn](fn1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True)

    A = Symbol(etype=dtype.integer)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Infer(Element(n, A), Equal(f[n], g[n])), wrt=n)

    Eq.suffice, Eq.necessary = algebra.iff.of.et.apply(Eq[0])

    Eq << Eq.suffice.this.lhs.apply(algebra.infer.then.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.ou.then.all, pivot=1, wrt=n)

    Eq << Eq.necessary.this.lhs.apply(algebra.infer.of.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.then.ou)


if __name__ == '__main__':
    run()
# created on 2018-09-18
