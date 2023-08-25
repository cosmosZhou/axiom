from util import *


@apply
def apply(self):
    expr, (k, S[0], n) = self.of(Sum)
    if expr.is_Pow:
        c, hk = expr.args
        assert not c._has(k)
        a, b = hk.of_simple_poly(k)
        coeff = c ** a
        λ = c ** b
    else:
        coeff = 1
        λ = 1
        for arg in expr.of(Mul):
            if not arg._has(k):
                coeff *= arg
            else:
                c, hk = arg.of(Pow)
                assert not c._has(k)
                a, b = hk.of_simple_poly(k)
                coeff *= c ** a
                λ *= c ** b

    return Equal(self, Piecewise((coeff * n, Equal(λ, 1)), (coeff * (1 - λ ** n) / (1 - λ), True)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    k, n = Symbol(integer=True)
    λ = Symbol(real=True)
    Eq << apply(Sum[k:n](λ ** k))

    Eq << algebra.cond_piece.given.et.infer.apply(Eq[0])

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.ne.imply.eq.sum.geometric_series, Eq[0].lhs)

    


if __name__ == '__main__':
    run()
# created on 2023-06-17
