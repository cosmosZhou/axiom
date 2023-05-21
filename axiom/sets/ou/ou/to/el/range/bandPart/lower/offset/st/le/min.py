from util import *


@apply
def apply(ou, ou_et):
    ((j, i), ((l, n), S[1])), ((S[i], S[Min(n, l) - 1]), (S[j], S[i])) = ou_et.of(Element[Expr - Expr, Range[1 - Min]] | Less & LessEqual)
    (S[j], S[i]), (S[i], S[Min(n, l) - 1]) = ou.of(LessEqual | GreaterEqual)
    
    assert i in Range(n) and j in Range(n)
    return Element(j - i, Range(-l + 1, 1))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, l = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(Or(j <= i, i >= Min(n, l) - 1), And(j <= i, i < Min(n, l) - 1) | Element(j - i, Range(1 - Min(n, l), 1)))

    Eq << Eq[0].this.find(Or[2]).apply(algebra.ou.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(And, And, Symbol <= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(algebra.et.distribute, 1)

    Eq << Eq[-1].this.find(Add < Add).apply(algebra.lt.transport, 0)

    Eq << -Eq[-1].this.find(-Symbol < Add)

    Eq << Eq[-1].this.lhs.apply(algebra.et.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol <= Symbol) - i

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(GreaterEqual[1 - Min]) - 1

    Eq << -Eq[-1].this.find(GreaterEqual[-Min])

    Eq << Eq[-1].this.find(LessEqual).apply(algebra.le_min.to.et.le)

    Eq << Eq[-1].this.find(LessEqual) - 1

    Eq << -Eq[-1].this.find(LessEqual)

    
    


if __name__ == '__main__':
    run()
# created on 2022-03-29
# updated on 2023-05-21
