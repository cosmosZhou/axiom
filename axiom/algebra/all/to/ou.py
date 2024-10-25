from util import *


@apply
def apply(imply):
    from axiom.algebra.all.then.ou import rewrite_as_Or
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.then.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.of.ou)


if __name__ == '__main__':
    run()

# created on 2018-12-23
