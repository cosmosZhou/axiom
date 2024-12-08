from util import *


@apply
def apply(given, index=-1):
    (p, q), r = given.of(Imply >> Boolean)
    return Imply(p.invert(), r), Imply(q, r)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, a, b = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Imply((x > b) >> (x < a), f(x) > g(y)))

    Eq << Eq[0].this.lhs.apply(Algebra.Imply.to.Or)
    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-23
