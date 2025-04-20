from util import *


@apply
def apply(self):
    x, s = self.of(NotElement)

    return Element(x, x.domain - s)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(NotElement(x, S))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.Mem.SDiff.of.NotMem)

    Eq << Eq[-1].this.rhs.apply(Set.NotMem.given.Mem.SDiff)




if __name__ == '__main__':
    run()
# created on 2023-05-21
