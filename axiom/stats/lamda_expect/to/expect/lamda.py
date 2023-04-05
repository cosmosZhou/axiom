from util import *


@apply
def apply(self, *, simplify=True):
    from axiom.stats.sum_expect.to.expect.sum import rewrite
    return Equal(self, rewrite(Lamda, self, simplify))


@prove
def prove(Eq):
    from axiom import stats

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    s = Symbol(real=True, random=True)
    Eq << apply(Lamda[k:n](Expectation(f(x[k]) | s)), simplify=False)

    Eq << Eq[-1].this.rhs.apply(stats.expect_lamda.to.lamda.expect)

    


if __name__ == '__main__':
    run()
# created on 2023-04-02
