from util import *


@apply
def apply(self, t):
    e, interval = self.of(Element)
    t = sympify(t)
    return Element(e + (-t), interval + (-t))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic
    x = Symbol(integer=True)
    a, b, t = Symbol(real=True)

    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Set.MemSub.of.Mem_Icc, t)

    Eq << Eq[-1].this.lhs.apply(Set.MemAdd.of.Mem_Icc, t)


if __name__ == '__main__':
    run()

# created on 2018-04-12
