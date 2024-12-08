from util import *


@apply
def apply(eq_x_given_yz, z_given_y):
    (z, y), S[z] = z_given_y.of(Equal[Conditioned])

    (x, yz), (S[x], S[y]) = eq_x_given_yz.of(Equal[Conditioned, Conditioned])

    _y, _z = yz.of(And)
    if _y != y:
        _z, _y = _y, _z

    assert _z == z or _z == z.as_boolean()
    assert _y == y

    return Equal(x | z, x)


@prove
def prove(Eq):
    from Axiom import Algebra, Stats, Calculus

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y & z, x | y), Equal(z | y, z))

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq.y_nonzero, Eq.yz_nonzero = Algebra.And.to.And.apply(Eq[-1])

    _, Eq.z_nonzero = Stats.Ne_0.to.And.Ne_0.apply(Eq.yz_nonzero)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq.yz_nonzero, x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq.y_nonzero, z)

    Eq << Eq[-2].subs(Eq[-1])

    Eq.xy_probability = Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq.y_nonzero, x)

    Eq << Eq[-1].subs(Eq.xy_probability.reversed)

    Eq << Eq[-1].subs(Eq[1])

    y_ = pspace(y).symbol
    Eq << Stats.Integral.eq.Prob.marginal.apply(Integral[y_](Eq[-1].lhs))

    Eq << Eq[-1].subs(Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq.z_nonzero, x))

    Eq << Calculus.Eq.to.Eq.Integral.apply(Eq[-3], (y_,))

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Integral).apply(Stats.Integral.eq.Prob.marginal)

    Eq << Algebra.Ne_0.Eq.to.Eq.scalar.apply(Eq[-1], Eq.z_nonzero)





if __name__ == '__main__':
    run()
# created on 2021-07-14
# updated on 2023-05-18
