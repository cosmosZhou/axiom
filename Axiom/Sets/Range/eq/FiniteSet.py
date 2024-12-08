from util import *


@apply
def apply(self):
    a, b = self.of(Range)
    size = b - a
    s = {a + i for i in range(size)}

    return Equal(self, s)


@prove
def prove(Eq):
    from Axiom import Sets
    a = Symbol(integer=True)

    Eq << apply(Range(a, a + 4))

    Eq << Eq[0].this.rhs.apply(Sets.FiniteSet.eq.Interval)


if __name__ == '__main__':
    run()

# created on 2018-04-25
