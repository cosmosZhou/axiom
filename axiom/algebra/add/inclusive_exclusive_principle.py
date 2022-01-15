from util import *


@apply
def apply(self):
    p, q = self.of(Add)
    p = p.of(Bool)
    q = q.of(Bool)

    return Equal(self, Bool(p | q) + Bool(p & q))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)

    Eq << apply(Bool(Element(x, A)) + Bool(Element(x, B)))

    Eq << Eq[-1].this.rhs.args[1].arg.apply(sets.el.to.ou.split.union)

    Eq << Eq[-1].this.find(Bool[Or]).apply(algebra.bool.to.add)


if __name__ == '__main__':
    run()

# created on 2018-08-03
