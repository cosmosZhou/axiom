from util import *


@apply
def apply(self, *, cond=None):
    p, q = self.of(Equivalent)
    return Equivalent(p | cond, q | cond)


@prove
def prove(Eq):
    from axiom import algebra

    p, q, r = Symbol(bool=True)
    Eq << apply(Equivalent(p, q), cond=r)

    Eq << algebra.iff.then.infer.apply(Eq[0])

    Eq << algebra.infer.then.infer.ou.apply(Eq[-1], cond=r)

    Eq << algebra.iff.then.assuming.apply(Eq[0])

    Eq << algebra.assuming.then.assuming.ou.apply(Eq[-1], cond=r)

    Eq << algebra.iff.of.et.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-01-27
