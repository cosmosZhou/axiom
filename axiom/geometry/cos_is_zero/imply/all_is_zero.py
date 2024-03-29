from util import *


@apply
def apply(is_zero, n=None, negative=False):
    x = is_zero.of(Equal[Cos, 0])
    if n is None:
        n = is_zero.generate_var(integer=True, var='n')

    Pi = -S.Pi if negative else S.Pi
    return All[n:oo](Equal(cos(x + n * Pi), 0))


@prove
def prove(Eq):
    from axiom import algebra, geometry

    x = Symbol(real=True, given=True)
    n = Symbol(integer=True, given=False, nonnegative=True)
    Eq << apply(Equal(cos(x), 0), n, negative=True)

    # Eq << Equal(cos(x + n * S.Pi), 0, plausible=True)
    Eq << Equal(cos(x - n * S.Pi), 0, plausible=True)

    Eq << Eq[-1].subs(n, 0)

    Eq.induct = Eq[-1].subs(n, n + 1)

    Eq << Eq.induct.this.find(Mul).apply(algebra.mul.to.add).reversed

    Eq << Eq[-1].this.lhs.apply(geometry.cos.neg)
    Eq << Infer(Eq[2], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq[0], Eq[-1], n=n, start=0)

    Eq << algebra.cond.imply.all.apply(Eq[2], n)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)
    


if __name__ == '__main__':
    run()
# created on 2018-06-18
# updated on 2023-05-20
