from util import *


@apply
def apply(el):
    i, (a, b) = el.of(Element[Range])
    a += 1
    b -= 1
    return Equal(Range(a, i) | Range(i + 1, b), Range(a, b) - {i})


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Element(i, Range(-1, n + 1)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[1])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Union.to.Or), Eq[-1].this.rhs.apply(Sets.In_Union.of.Or)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Complement.of.And, simplify=False), Eq[-1].this.lhs.apply(Sets.In_Complement.to.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.equ.And), Eq[-1].this.find(Element).apply(Sets.In_Range.equ.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.equ.And), Eq[-1].this.find(Element).apply(Sets.In_Range.equ.And)

    Eq <<= Eq[-2].this.find(Element).apply(Sets.In_Range.equ.And), Eq[-1].this.find(Element).apply(Sets.In_Range.equ.And)

    Eq << Eq[-1].this.rhs.find(GreaterEqual).apply(Algebra.Ge.equ.Gt.strengthen)

    Eq << Eq[-2].this.find(NotElement).simplify()

    Eq << Eq[-1].this.find(Symbol >= Add).apply(Algebra.Ge.equ.Gt.strengthen)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-1]), Algebra.Imply.of.And.Imply.apply(Eq[-2])

    Eq <<= Algebra.Imply_And.of.Imply.delete.apply(Eq[-4]), Algebra.Imply_And.of.Imply.delete.apply(Eq[-3]), Algebra.Imply_And.of.Imply.delete.apply(Eq[-2], 0), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1], 0)

    Eq <<= Algebra.Imply.of.Or.apply(Eq[-4]), Algebra.Imply.of.Or.apply(Eq[-3]), Algebra.Imply.of.Or.apply(Eq[-2]), Algebra.Imply.of.Or.apply(Eq[-1])

    Eq <<= Sets.Or.of.NotIn.Range.apply(Eq[-2]), Sets.Or.of.NotIn.Range.apply(Eq[-1])

    Eq <<= Sets.NotIn.of.Eq_EmptySet.apply(Eq[-2]), Sets.NotIn.of.Eq_EmptySet.apply(Eq[-1])

    Eq << Sets.In_Range.to.And.apply(Eq[0])

    Eq << Sets.Ge.to.Eq_EmptySet.Range.apply(Eq[-2] + 1)

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq << Sets.Le.to.Eq_EmptySet.Range.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-28
# updated on 2023-05-20
