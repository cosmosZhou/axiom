from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_real
    return Element(x, Reals - {0})


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True)
    Eq << apply(Unequal(x, 0))

    Eq << Algebra.Ne_0.to.Or.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(Sets.Gt_0.to.is_positive, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Sets.Lt_0.to.is_negative, simplify=None)

    Eq << Sets.Or.to.In.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-02
