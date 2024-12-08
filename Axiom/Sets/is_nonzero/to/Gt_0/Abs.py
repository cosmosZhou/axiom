from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Sets.In_Union.to.Or.apply(Eq[0], simplify=None)

    Eq.is_negative = Imply(Eq[-1].args[1], Eq[1], plausible=True)

    Eq << Eq.is_negative.this.lhs.apply(Sets.is_negative.to.Lt_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.to.Ne_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.to.Gt_0.Abs)

    Eq.is_positive = Imply(Eq[2].args[0], Eq[1], plausible=True)

    Eq << Eq.is_positive.this.lhs.apply(Sets.is_positive.to.Gt_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Ne_0)

    Eq << Algebra.Imply.Imply.to.Imply.Or.apply(Eq.is_negative, Eq.is_positive)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2020-04-11
# updated on 2023-05-12
