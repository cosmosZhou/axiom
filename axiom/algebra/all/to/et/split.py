from util import *


@apply
def apply(self, *, cond=None, wrt=None, evaluate=False):
    from axiom.algebra.sum.to.add.split import split
    return split(All, self, cond, wrt=wrt)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(All[x:A](f(x) > 0), cond=B)

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(algebra.all.all.of.all.limits_union)

    Eq << Eq[-1].this.lhs.apply(algebra.all.all.then.all.limits_union)


if __name__ == '__main__':
    run()

# created on 2018-04-23
