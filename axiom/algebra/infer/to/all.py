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

    Eq.suffice, Eq.necessary = algebra.iff.given.et.apply(Eq[0])

    Eq << Eq.suffice.this.lhs.apply(algebra.infer.imply.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.ou.imply.all, pivot=1, wrt=n)

    Eq << Eq.necessary.this.lhs.apply(algebra.infer.given.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.imply.ou)


if __name__ == '__main__':
    run()
# created on 2018-09-18
