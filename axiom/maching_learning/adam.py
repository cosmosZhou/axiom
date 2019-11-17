from sympy.core.symbol import Symbol
from sympy.core.numbers import oo
from sympy.utility import Sum, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase


def extract(recurrence):
    lhs, rhs = recurrence.args
    t, *_ = lhs.indices
    m = lhs.base

    p = rhs.as_poly(m[t - 1])
    if p is None or p.degree() != 1:
        return None
    beta = p.coeff_monomial(m[t - 1])
    beta_gt = p.coeff_monomial(1)

    gt = beta_gt / (1 - beta)
    gt = gt.ratsimp()

    g = gt.base
    return m, g, beta, t


def apply(*given):
    if given:
        initial_condition, recurrence = given

        m, g, beta, t = extract(recurrence)
    else:
        m = IndexedBase('m', shape=(oo,))
        g = IndexedBase('g', shape=(oo,))
        t = Symbol('t', integer=True, positive=True)
        beta = Symbol('beta', nonzero=True)
        recurrence = Equality(m[t], beta * m[t - 1] + (1 - beta) * g[t])
        initial_condition = Equality(m[0], 0)
        given = [initial_condition, recurrence]

    k = Symbol('k', integer=True, nonnegative=True)

    return Equality(m[k], beta ** k * (1 - beta) * Sum[t:1:k](beta ** (-t) * g[t]),
                    given=given,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    Eq << apply()

    Eq << Eq[-1].given

    m, g, beta, t = extract(Eq[-1])

    Eq << Eq[-1] / beta ** t

    Eq << Eq[-1].expand()

    Eq << Eq[-1].powsimp()

    Eq << Eq[-1].collect(g[t])

    k = Eq[0].lhs.indices[0]

    Eq << Eq[-1].summation((t, 1, k))

    Eq << Eq[-1].this.rhs.as_two_terms()

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.simplifier()

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].solve(m[k])

#     Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove(__file__)
