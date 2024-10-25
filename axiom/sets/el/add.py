from util import *


@apply
def apply(self, t):
    t = sympify(t)
    e, interval = self.of(Element)

    return Element(e + t, interval + t)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.then.el.add, t), Eq[-1].this.lhs.apply(sets.el.of.el.add, t)




if __name__ == '__main__':
    run()
# created on 2020-02-27
# updated on 2023-05-31
