from util import *


@apply
def apply(self):
    a, b = self.of(Range)
    size = b - a
    s = {a + i for i in range(size)}

    return Equal(self, s)


@prove
def prove(Eq):
    from axiom import sets
    a = Symbol(integer=True)

    Eq << apply(Range(a, a + 4))

    Eq << Eq[0].this.rhs.apply(sets.finiteset.to.interval)


if __name__ == '__main__':
    run()

