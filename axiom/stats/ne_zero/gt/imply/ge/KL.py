from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, gt):
    m, n = gt.of(Greater)
    assert m > 0 and n > 0
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Probability[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Probability[Equal], 0])

    return GreaterEqual(KL(Probability(Equal(x_lhs, x_var), *weights_lhs), Probability(Equal(x_rhs, x_var), *weights_rhs)),
                        KL(Probability(Equal(x_lhs[:n], x_var[:n]), *weights_lhs), Probability(Equal(x_rhs[:n], x_var[:n]), *weights_rhs)))

@prove
def prove(Eq):
    from axiom import stats

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True, shape=(oo,))
    Eq << apply(Unequal(Probability[θ](x[:m]), 0),
                Unequal(Probability[θ_quote](x[:m]), 0),
                m > n)

    Eq << stats.ne_zero.gt.imply.et.ne_zero.apply(Eq[0], Eq[2])

    Eq << stats.ne_zero.gt.imply.et.ne_zero.apply(Eq[1], Eq[2])

    # notes: it is illegal to access x[n:m] because it is not proven to be existent due to indexOutOfBound error
    # we can only access it through a proven result that containing the expression we want
    Eq << stats.ne_zero.ne_zero.imply.ge.KL.pdf.apply(Eq[-4], Eq[-2], Eq[-1].lhs.arg.lhs)

    Eq << stats.gt.imply.eq.prob.joint.apply(Eq[2], Eq[0].lhs)

    Eq << stats.gt.imply.eq.prob.joint.apply(Eq[2], Eq[1].lhs)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    


if __name__ == '__main__':
    run()
# created on 2023-03-26
