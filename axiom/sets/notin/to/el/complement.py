from util import *


@apply
def apply(self):
    x, s = self.of(NotElement)

    return Element(x, x.domain - s)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(NotElement(x, S))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.notin.then.el.complement)

    Eq << Eq[-1].this.rhs.apply(sets.notin.of.el.complement)




if __name__ == '__main__':
    run()
# created on 2023-05-21
