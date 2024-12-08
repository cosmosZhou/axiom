from util import *


@apply
def apply(ou, ou_et):
    ((j, i), (S[0], (n, u))), ((S[j], S[i]), (S[i], S[n - Min(n, u)])) = ou_et.of(Element[Expr - Expr, Range[Min]] | GreaterEqual & GreaterEqual)
    (S[j], S[i]), (S[i], S[n - Min(n, u)]) = ou.of(GreaterEqual | Less)

    assert i in Range(n) and j in Range(n)
    return Element(j - i, Range(0, u))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n, u = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(And(j >= i, i >= n - Min(n, u)) | Element(j - i, Range(Min(n, u))), Or(j >= i, i < n - Min(n, u)))

    Eq << Eq[0].this.find(Or[2]).apply(Algebra.Or.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Range.equ.Or)

    Eq << Eq[-1].this.find(And, And, Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(Algebra.And.distribute, 1)

    Eq << Eq[-1].this.find(Add >= Min).apply(Algebra.Ge.transport, lhs=0)

    Eq << -Eq[-1].this.find(-Symbol >= Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Range.equ.Or)

    Eq << Eq[-1].this.find(Range).apply(Sets.Range.Min.eq.Intersect)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Intersect.equ.And)

    Eq << Eq[-1].this.lhs.find(Element).apply(Sets.In_Range.equ.And)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.equ.And)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.equ.And)





if __name__ == '__main__':
    run()
# created on 2022-03-30
# updated on 2023-05-21
