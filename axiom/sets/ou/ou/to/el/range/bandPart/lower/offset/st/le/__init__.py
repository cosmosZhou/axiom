from util import *


@apply
def apply(ou, ou_et):
    ((i, l), (j, S[i])), ((S[j], S[i]), (S[l + 1], S[1])) = ou_et.of(Less & LessEqual | Element[Expr - Expr, Range[1 - Expr]])
    (S[j], S[i]), (S[i], S[l]) = ou.of(LessEqual | GreaterEqual)
    
    assert i >= 0
    assert j >= 0
    l += 1
    return Element(j - i, Range(-l + 1, 1))


@prove
def prove(Eq):
    from axiom import algebra, sets

    l = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(integer=True, nonnegative=True)
    Eq << apply(And(j <= i, i < l - 1) | Element(j - i, Range(1 - l, 1)), Or(j <= i, i >= l - 1))

    Eq << Eq[0].this.find(Or[Element]).apply(algebra.ou.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Or, And, Symbol <= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(algebra.et.distribute, 1)

    Eq << Eq[-1].this.find(Add < Add).apply(algebra.lt.transport, 0)

    Eq << -Eq[-1].this.find(-Symbol < Add)

    Eq << Eq[-1].this.lhs.apply(algebra.et.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol <= Symbol) - i

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-02
# updated on 2023-05-21

from . import min
