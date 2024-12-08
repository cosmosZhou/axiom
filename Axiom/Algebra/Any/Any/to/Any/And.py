from util import *


@apply
def apply(any_x, any_y):
    from Axiom.Algebra.All.Any.to.Any.All.And import limits_dependent
    fx, *limits_x = any_x.of(Any)
    fy, *limits_y = any_y.of(Any)

    assert not limits_dependent(limits_x, limits_y)

    return Any(fx & fy, *limits_x, *limits_y)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Any[x:A](f(x, y) > 0), Any[y:B](g(y, x) > 0))

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.Any.to.Any.And)


if __name__ == '__main__':
    run()

# created on 2019-02-08
