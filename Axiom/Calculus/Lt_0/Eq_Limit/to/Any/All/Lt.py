from util import *


@apply
def apply(is_positive, eq, delta=None):
    A = is_positive.of(Expr < 0)
    (fx, (x, x0)), S[A] = eq.of(Equal[Limit])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    x0, epsilon = x0.clear_infinitesimal()
    if epsilon > 0:
        cond = Interval.open(x0, x0 + delta)
    elif epsilon < 0:
        cond = Interval.open(x0 - delta, x0)
    else:
        cond = (abs(x - x0) > 0) & (abs(x - x0) < delta)

    return Any[delta](All[x:cond](fx < A / 2))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    x, A, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(A < 0, Equal(Limit[x:x0](f(x)), A))

    epsilon = Symbol(positive=True)
    delta = Eq[-1].variable
    Eq << Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[1], epsilon, delta)

    Eq << Algebra.Cond.to.Or.subs.apply(Eq[-1], epsilon, -A / 2)

    Eq << Algebra.Cond.Or.to.Cond.apply(-Eq[0] / 2, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.to.And.split.Abs)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.And.to.Cond)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.transport, lhs=0)





if __name__ == '__main__':
    run()
# created on 2020-05-14
# updated on 2023-10-15