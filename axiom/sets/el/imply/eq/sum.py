from util import *


@apply
def apply(contains, sgm):
    fi, (i, m) = sgm.of(Sum[Tuple[0]])
    t, s = contains.of(Element)
    assert s in Range(m)

    return Equal(sgm, Sum[i:Range(m) - {t}](fi) + fi._subs(i, t))


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    x, y = Function(real=True)
    i, j = Symbol(integer=True)
    t = Symbol(integer=True, given=True)
    Eq << apply(Element(t, Range(m)), Sum[j:m](y(j)))

    Eq << Eq[1].this.lhs.apply(algebra.sum.to.add.split, cond={t})
    Eq << algebra.cond.imply.eq.piece.apply(Eq[0], Eq[-1].lhs)


if __name__ == '__main__':
    run()
# created on 2021-03-09
# updated on 2021-03-09
