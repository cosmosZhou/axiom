from util import *


@apply
def apply(self, index):
    [*eqs] = self.of(Or)
    p = eqs[index]
    if isinstance(index, slice):
        p = Or(*p)

    del eqs[index]
    q = Or(*eqs)

    return Assuming(q, p.invert())


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    B = Symbol(etype=dtype.integer)
    f, g = Function(integer=True)
    Eq << apply(Or(x <= y, f(x) > g(y), Element(y, B)), index=slice(1, 3))

    Eq << Eq[-1].this.rhs.apply(algebra.assuming.to.ou)
    


if __name__ == '__main__':
    run()
# created on 2020-02-20
# updated on 2023-05-21
