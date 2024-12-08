from util import *


@apply
def apply(self, *, simplify=True):
    from Axiom.Stats.Sum.Expect.eq.Expect.Sum import rewrite
    return Equal(self, rewrite(Lamda, self, simplify))


@prove
def prove(Eq):
    from Axiom import Stats

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    s = Symbol(real=True, random=True)
    Eq << apply(Lamda[k:n](Expectation(f(x[k]) | s)), simplify=False)

    Eq << Eq[-1].this.rhs.apply(Stats.Expect.Lamda.eq.Lamda.Expect)




if __name__ == '__main__':
    run()
# created on 2023-04-02
