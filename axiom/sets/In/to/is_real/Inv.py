from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R == Reals - {0}

    return Element(1 / x, Reals)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Sets.In_Union.to.Or.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[1].apply(Sets.In.to.In.Inv.Interval, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Sets.In.to.In.Inv.Interval, simplify=False)

    Eq << Subset(Eq[-1].rhs, Eq[1].rhs, plausible=True)

    Eq << Sets.In.Subset.to.In.apply(Eq[-2], Eq[-1], simplify=None)





if __name__ == '__main__':
    run()
# created on 2020-06-21
# updated on 2023-05-12
