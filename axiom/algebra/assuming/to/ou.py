from util import *



@apply
def apply(given):
    p, q = given.of(Assuming)
    return p | q.invert()


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Assuming(x > y, f(x) > g(y)))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.assuming.imply.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.assuming.given.ou)

if __name__ == '__main__':
    run()
# created on 2019-03-02
