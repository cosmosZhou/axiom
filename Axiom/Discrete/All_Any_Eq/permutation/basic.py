from util import *



@apply
def apply(n):
    i = Symbol(integer=True)

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))

    return All[p[:n]:P](Any[i:n](Equal(p[i], n - 1)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << Eq[1].subs(Eq[0])

    Eq << Algebra.All.limits_assert.apply(Eq[-1].limits)

    Eq << Element(n - 1, Eq[-1].rhs, plausible=True)

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.to.Any_In)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-08-31
