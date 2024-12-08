from util import *



@apply
def apply(given, wrt=None):
    fn, fn1 = given.of(Imply)
    if wrt is None:
        wrt = fn.wrt
    assert wrt.is_given is None
    return All[wrt:fn](fn1)


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True)

    A = Symbol(etype=dtype.integer)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Imply(Element(n, A), Equal(f[n], g[n])), wrt=n)

    Eq.suffice, Eq.necessary = Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq.suffice.this.lhs.apply(Algebra.Imply.to.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.to.All, pivot=1, wrt=n)

    Eq << Eq.necessary.this.lhs.apply(Algebra.Imply.of.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.to.Or)


if __name__ == '__main__':
    run()
# created on 2018-09-18
