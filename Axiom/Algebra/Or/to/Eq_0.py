from util import *


@apply
def apply(given):
    or_eqs = given.of(Or)

    args = []
    for eq in or_eqs:
        lhs, rhs = eq.of(Equal)
        args.append(lhs - rhs)
    mul = Mul(*args)
    return Equal(mul, ZeroMatrix(*mul.shape))


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, f(x)) | Equal(p, g(x)) | Equal(p, h(x)))

    Eq <<= ~Eq[1] & Eq[0]

    Eq << Eq[-1].this.args[0].apply(Algebra.Ne_0.to.And.Matrix)

    Eq << Eq[-1].this.find(Unequal[ZeroMatrix]).apply(Algebra.Ne_0.to.And.Matrix)

    Eq << Algebra.And.to.Or.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-01-26
# updated on 2023-05-15

