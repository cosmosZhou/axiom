from util import *


@apply
def apply(self):
    n, d = self.of(Mod)
    assert n.is_integer
    assert d.is_integer
    assert d > 0
    return Element(self, Range(d))


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    n = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(n % d)

    Eq << Eq[0].this.lhs.apply(Algebra.Mod.eq.Sub_Mul_Div)

    Eq << Set.Mem_Range.given.And.apply(Eq[-1])



    Eq <<= Eq[-2] - n, Eq[-1] - n

    Eq <<= -Eq[-2], -Eq[-1]

    Eq <<= Eq[-2] / d, Eq[-1] / d

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Algebra.Floor.gt.Sub_1.apply(n / d)


if __name__ == '__main__':
    run()

# created on 2018-03-02
