from util import *


@apply
def apply(given):
    ((f, (z, xi)), _f), (S[xi], domain) = given.of(All[Equal[Limit]])
    assert not xi.infinitesimality
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert _f == f._subs(z, xi)
    assert b >= a
    return Any[xi:domain](Equal(Integral(f, (z, a, b)), (b - a) * _f))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from Axiom.Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    z = Eq[0].lhs.args[1][0]
    m = Symbol(Minima[z:Interval(a, b)](f(z)))
    M = Symbol(Maxima[z:Interval(a, b)](f(z)))
    Eq.min = m.this.definition

    Eq.max = M.this.definition

    Eq << Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem.apply(Eq[0])

    Eq.intermediate_value = Eq[-1].subs(Eq.max.reversed).subs(Eq.min.reversed)

    Eq << Algebra.All_LeMinima.apply(m.definition)

    Eq << Calculus.All_Le.to.Le.Integral.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.min.reversed) / (b - a)

    Eq << Algebra.All_GeMaxima.apply(M.definition)

    Eq << Calculus.All_Ge.to.Ge.Integral.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.max.reversed) / (b - a)

    Eq <<= Sets.Le.Ge.to.In.Interval.apply(Eq[-4], Eq[-1])

    Eq << Algebra.All.to.Or.subs.apply(Eq.intermediate_value, Eq.intermediate_value.rhs, Eq[-1].lhs)

    Eq << Algebra.Or.to.Any.Or.apply(Eq[-1], simplify=None)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << Algebra.Any_And.to.AndAnyS.apply(Eq[-1])

    Eq << Eq[-1].this.expr * (b - a)

    Eq << Eq[-1].this.expr.rhs.ratsimp().reversed





if __name__ == '__main__':
    run()

# created on 2020-06-15
# updated on 2023-05-04
