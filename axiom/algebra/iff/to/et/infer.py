from util import *


@apply
def apply(self):
    p, q = self.of(Equivalent)
    return And(Infer(p, q), Infer(q, p))


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(bool=True)
    Eq << apply(Equivalent(p, q))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(algebra.infer.infer.of.iff)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.infer.then.iff)


if __name__ == '__main__':
    run()
# created on 2022-01-27
