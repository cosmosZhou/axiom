from util import *


@apply
def apply(any_x, any_y):
    from axiom.algebra.all.any.imply.any.all.et import limits_dependent
    fx, *limits_x = any_x.of(Any)
    fy, *limits_y = any_y.of(Any)

    assert not limits_dependent(limits_x, limits_y)

    return Any(fx & fy, *limits_x, *limits_y)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Any[x:A](f(x, y) > 0), Any[y:B](g(y, x) > 0))

    Eq << algebra.cond.any.imply.any.et.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.expr.apply(algebra.cond.any.imply.any.et)


if __name__ == '__main__':
    run()

# created on 2019-02-08
