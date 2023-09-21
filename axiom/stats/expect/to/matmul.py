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
    from axiom import algebra, stats, discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    Eq << apply(Expectation(A @ x[:n] | s))

    Eq << Eq[0].this.rhs.find(Sliced).apply(algebra.slice.to.lamda)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.lamda.to.lamda.expect)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Mul).apply(stats.mul.to.expect)

    Eq << Eq[-1].this.find(Sum).apply(stats.sum.expect.to.expect.sum)

    Eq << Eq[-1].this.find(Lamda).apply(stats.lamda.expect.to.expect.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda.to.matmul)




if __name__ == '__main__':
    run()
# created on 2023-04-07
