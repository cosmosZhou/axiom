from util import *


@apply
def apply(self, *, simplify=True):
    x, *limits = self.of(Lamda[Exp])

    x_exp = Lamda(exp(x), *limits)
    x = Lamda(x, *limits)

    if simplify:
        x_exp = x_exp.simplify()
        x = x.simplify()

    return Equal(self, Softmax(x) * ReducedSum(x_exp))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, positive=True)
    x = Symbol(shape=(m, n), real=True)
    i = Symbol(integer=True)
    Eq << apply(Lamda[i:m](exp(x[i])))

    Eq << Eq[0].this.lhs.apply(Algebra.Lamda.eq.Exp)

    Eq << Eq[-1].this.lhs.apply(Neuro.Exp.eq.Mul.Softmax)



if __name__ == '__main__':
    run()
# created on 2022-01-10
