from util import *


@apply(simplify=False)
def apply(imply):
    fn, (x, cond, baseset) = imply.of(All)
    return All[x:cond:baseset](fn & cond)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(integer=True)
    f, g = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer)

    Eq << apply(All[x:g(x) > 0:A](f(x) > 0))

    Eq << Algebra.All_And.to.All.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-12-11