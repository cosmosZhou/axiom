from util import *


@apply
def apply(lt, self):
    d, n = lt.of(Less)
    (fx, S[d]), (x, S[n]) = self.of(Difference[Pow])
    assert not (fx - x)._has(x)
    return Equal(self, 0)


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Set, Logic

    x = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    Eq << apply(d < n, Difference(x ** d, (x, n)))

    d_quote = Symbol(domain=Range(n))
    Eq << Discrete.Diff.eq.Zero.apply(Difference(x ** d_quote, (x, n)))

    Eq << Algebra.All.of.Cond.apply(Eq[-1], d_quote)

    Eq << Logic.Imp.of.All.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-2].variable, d)

    Eq << Eq[-1].this.lhs.apply(Set.Mem_Range.given.And)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2021-12-01
