from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    b, e = self.of(Pow)
    assert b == -1
    assert e.is_integer
    return Element(self, {-1, 1})


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    n = Symbol(integer=True)

    Eq << apply((-1) ** n)

    p = Symbol((-1) ** n)
    Eq << Equal(abs(p), 1, plausible=True)

    Eq << Eq[-1].this.lhs.arg.definition

    Eq << Algebra.Eq_Abs.to.Or.apply(Eq[-1])

    Eq << Sets.Or_Eq.to.In.FiniteSet.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()

# created on 2020-03-01
