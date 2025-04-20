from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.Sum.limits.subs.Neg import limits_subs
    return Equal(self, limits_subs(Cap, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Set

    i, a, b, c = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Set.Cap.eq.Cap_Ite)

    Eq << Eq[-1].this.rhs.apply(Set.Cap.limits.Neg.Infty)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.Mem.Neg)

    Eq << Eq[-1].this.rhs.apply(Set.Cap.limits.subs.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.Mem_Icc.Is.MemAdd, c)

    Eq << Eq[-1].this.lhs.apply(Set.Cap.eq.Cap_Ite)


if __name__ == '__main__':
    run()
# created on 2021-01-28
