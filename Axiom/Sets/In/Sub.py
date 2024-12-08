from util import *


@apply
def apply(self, t):
    e, interval = self.of(Element)
    t = sympify(t)
    return Element(e + (-t), interval + (-t))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    x = Symbol(integer=True)
    a, b, t = Symbol(real=True)

    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Sets.In.to.In.Sub, t)

    Eq << Eq[-1].this.rhs.apply(Sets.In.to.In.Add, t)


if __name__ == '__main__':
    run()

# created on 2018-04-12
