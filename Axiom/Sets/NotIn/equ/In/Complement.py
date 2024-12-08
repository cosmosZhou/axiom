from util import *


@apply
def apply(self):
    x, s = self.of(NotElement)

    return Element(x, x.domain - s)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(NotElement(x, S))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.NotIn.to.In.Complement)

    Eq << Eq[-1].this.rhs.apply(Sets.NotIn.of.In.Complement)




if __name__ == '__main__':
    run()
# created on 2023-05-21
