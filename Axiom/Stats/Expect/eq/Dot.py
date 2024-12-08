from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    [*args] = expr.of(MatMul)
    scope_variables = self.scope_variables
    from sympy.tensor.indexed import index_intersect
    for i, arg in enumerate(args):
        if index_intersect(arg.random_symbols, scope_variables):
            args[i] = Expectation(arg, *limits, given=given)

    return Equal(self, MatMul(*args))


@prove
def prove(Eq):
    from Axiom import Algebra, Stats, Discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    Eq << apply(Expectation(A @ x[:n] | s))

    Eq << Eq[0].this.rhs.find(Sliced).apply(Algebra.Slice.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Stats.Expect.Lamda.eq.Lamda.Expect)

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.find(Mul).apply(Stats.Mul.eq.Expect)

    Eq << Eq[-1].this.find(Sum).apply(Stats.Sum.Expect.eq.Expect.Sum)

    Eq << Eq[-1].this.find(Lamda).apply(Stats.Lamda.Expect.eq.Expect.Lamda)

    Eq << Eq[-1].this.find(Lamda).apply(Discrete.Lamda.eq.Dot)




if __name__ == '__main__':
    run()
# created on 2023-04-07
