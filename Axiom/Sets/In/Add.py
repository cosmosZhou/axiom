from util import *


@apply
def apply(self, t):
    t = sympify(t)
    e, interval = self.of(Element)

    return Element(e + t, interval + t)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In.to.In.Add, t), Eq[-1].this.lhs.apply(Sets.In.of.In.Add, t)




if __name__ == '__main__':
    run()
# created on 2020-02-27
# updated on 2023-05-31
