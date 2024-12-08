from util import *



@apply
def apply(given):
    p, q = given.of(Given)
    return p | q.invert()


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Given(x > y, f(x) > g(y)))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.Given.to.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.Given.of.Or)

if __name__ == '__main__':
    run()
# created on 2019-03-02
