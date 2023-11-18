from util import *


@apply
def apply(self):
    q, p = self.of(Assuming)
    return Assuming(p.invert(), q.invert())


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(bool=True)
    Eq << apply(Assuming(p, q))

    Eq << Eq[0].this.lhs.apply(algebra.assuming.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.assuming.to.ou)

    


if __name__ == '__main__':
    run()
# created on 2019-03-02
# updated on 2022-01-27
