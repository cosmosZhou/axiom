from util import *


@apply
def apply(self):
    p, q = self.of(Equivalent)
    return (p.invert() & q.invert()) | (p & q)


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(bool=True)
    Eq << apply(Equivalent(p, q))

    Eq << Eq[0].this.lhs.apply(algebra.iff.to.et.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.et.to.ou)

    


if __name__ == '__main__':
    run()
# created on 2022-01-27
