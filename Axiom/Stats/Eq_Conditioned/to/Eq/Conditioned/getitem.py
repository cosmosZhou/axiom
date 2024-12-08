from util import *


@apply
def apply(given, wrt=None):

    (x, given), S[x] = given.of(Equal[Conditioned[And]])

    if wrt is None:
        wrt = 0

    if isinstance(wrt, int):
        wrt = given[wrt]
    elif isinstance(wrt, slice):
        wrt = And(*given[wrt])
    else:
        wrt = wrt.as_boolean()
        assert wrt in given

    return Equal(x | wrt, x)


@prove
def prove(Eq):
    from Axiom import Algebra, Stats, Calculus

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y & z, x))

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq.y_nonzero, Eq.z_nonzero = Stats.Ne_0.to.And.Ne_0.apply(Eq[-1])

    Eq.xy_probability = Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq.y_nonzero, x)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[2], x)

    Eq << Eq[-1].subs(Eq[0])

    Eq <<= Stats.Integral.eq.Prob.marginal.apply(Integral[z.var](Eq[-1].lhs)), \
        Stats.Integral.eq.Prob.marginal.apply(Integral[z.var](Eq[2].lhs)), \
        Calculus.Eq.to.Eq.Integral.apply(Eq[-1], (z.var,))

    Eq << Eq[-3].subs(Eq.xy_probability)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq[-4])

    Eq << Algebra.Ne_0.Eq.to.Eq.scalar.apply(Eq[-1], Eq.y_nonzero)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()

# created on 2020-12-13
# updated on 2023-05-14
