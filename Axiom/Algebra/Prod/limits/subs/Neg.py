from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.Sum.limits.subs.Neg import limits_subs
    return Equal(self, limits_subs(Product, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Product[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.Bool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.Neg.Infty)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.Mem.Neg)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.subs.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.Mem_Icc.Is.MemAdd, c)

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.Bool)


if __name__ == '__main__':
    run()
# created on 2020-02-27
