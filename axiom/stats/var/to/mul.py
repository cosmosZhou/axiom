from util import *


@apply
def apply(self):
    expr, *limits = self.of(Variance)
    if expr.is_Mul:
        args = expr.args
        given = None
    else:
        args, given = expr.of(Conditioned[Mul])
    
    scope_variables = self.scope_variables
    
    variable = []
    constant = []
    for arg in args:
        if any(any(V.index_contains(v) for V in scope_variables) for v in arg.random_symbols):
            variable.append(arg)
        else:
            constant.append(arg)
            assert not arg.shape

    constant = Mul(*constant)
    variable = Mul(*variable)
    return Equal(self, constant ** 2 * Variance(variable, *limits, given=given))


@prove
def prove(Eq):
    from axiom import stats, algebra

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f, g = Function(real=True)
    a = Symbol(integer=True, random=True)
    b = Symbol(integer=True)
    Eq << apply(Variance[a:θ](f(a) * g(b)))

    Eq << Eq[-1].this.lhs.apply(stats.var.to.sub.expect)

    Eq << Eq[-1].this.find(Variance).apply(stats.var.to.sub.expect)

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find((~Expectation) ** 2).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul)


if __name__ == '__main__':
    run()
# created on 2023-04-19
