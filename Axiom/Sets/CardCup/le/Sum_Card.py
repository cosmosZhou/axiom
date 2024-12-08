from util import *


@apply
def apply(expr, *limits):
    return LessEqual(Card(Cup(expr, *limits)), Sum(Card(expr), *limits).simplify())


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)

    Eq << apply(A[k], (k, 0, n + 1))

    Eq << Eq[0].subs(n, 1)

    Eq << Eq[-1].this.lhs.doit(deep=True)

    Eq << Eq[-1].this.rhs.doit(deep=True)

    Eq << Sets.CardUnion.le.AddCardS.apply(*Eq[-1].lhs.arg.args)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.arg.apply(Sets.Cup.eq.Union.split, cond=slice(-1))

    Eq << Sets.CardUnion.le.AddCardS.apply(*Eq[-1].lhs.arg.args)

    Eq << Algebra.Le.Le.to.Le.subs.apply(Eq[-1], Eq[0])

    Eq << Eq.induct.this.rhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq[1], Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-07-07
