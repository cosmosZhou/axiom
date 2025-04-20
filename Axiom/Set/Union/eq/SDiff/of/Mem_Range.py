from util import *


@apply
def apply(el):
    i, (a, b) = el.of(Element[Range])
    a += 1
    b -= 1
    return Equal(Range(a, i) | Range(i + 1, b), Range(a, b) - {i})


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Element(i, Range(-1, n + 1)))

    Eq << Set.Eq.given.And.Imp.apply(Eq[1])

    Eq <<= Eq[-2].this.lhs.apply(Set.Or.of.Mem_Union), Eq[-1].this.rhs.apply(Set.Mem_Union.given.OrMemS)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_SDiff.given.And, simplify=False), Eq[-1].this.lhs.apply(Set.Mem.et.NotMem.of.Mem_SDiff)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.Is.And), Eq[-1].this.find(Element).apply(Set.Mem_Range.Is.And)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.Is.And), Eq[-1].this.find(Element).apply(Set.Mem_Range.Is.And)

    Eq <<= Eq[-2].this.find(Element).apply(Set.Mem_Range.Is.And), Eq[-1].this.find(Element).apply(Set.Mem_Range.Is.And)

    Eq << Eq[-1].this.rhs.find(GreaterEqual).apply(Algebra.Ge.Is.Gt.strengthen)

    Eq << Eq[-2].this.find(NotElement).simplify()

    Eq << Eq[-1].this.find(Symbol >= Add).apply(Algebra.Ge.Is.Gt.strengthen)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-1]), Logic.Imp_And.given.Imp.Imp.apply(Eq[-2])

    Eq <<= Logic.Imp_And.given.Imp.delete.apply(Eq[-4]), Logic.Imp_And.given.Imp.delete.apply(Eq[-3]), Logic.Imp_And.given.Imp.delete.apply(Eq[-2], 0), Logic.Imp_And.given.Imp.delete.apply(Eq[-1], 0)

    Eq <<= Logic.Imp.given.Or_Not.apply(Eq[-4]), Logic.Imp.given.Or_Not.apply(Eq[-3]), Logic.Imp.given.Or_Not.apply(Eq[-2]), Logic.Imp.given.Or_Not.apply(Eq[-1])

    Eq <<= Set.Or.given.NotMem.Range.apply(Eq[-2]), Set.Or.given.NotMem.Range.apply(Eq[-1])

    Eq <<= Set.NotMem.given.Eq_EmptySet.apply(Eq[-2]), Set.NotMem.given.Eq_EmptySet.apply(Eq[-1])

    Eq << Set.And.of.Mem_Range.apply(Eq[0])

    Eq << Set.Eq_EmptySet.Range.of.Ge.apply(Eq[-2] + 1)

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[-1])

    Eq << Set.Eq_EmptySet.Range.of.Le.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-28
# updated on 2023-05-20
