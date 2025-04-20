from util import *


@apply
def apply(given):
    e, (_, s)= given.of(Element[Complement])
    return Equal(Bool(NotElement(e, s)), 1)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic
    e = Symbol(integer=True)
    s, S = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, S - s))

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Set.NotMem.of.Mem_SDiff.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-03-06
