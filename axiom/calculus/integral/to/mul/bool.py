from util import *


@apply
def apply(self):
    expr, (x, domain) = self.of(Integral)
    a, b = domain.of(Interval)
    return Equal(self, Integral[x:a:b](expr) * Bool(a <= b))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:Interval(a, b)](f(x)))

    Eq << Eq[0].this.rhs.find(Integral).apply(calculus.integral.to.piece)

    Eq << Eq[-1].this.rhs.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.piece.to.piece)

    Eq << algebra.cond_piece.of.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.gt.then.is_empty.interval)

    Eq << algebra.infer.of.infer.subs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-19
