from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    if expr.is_Mul:
        args = expr.args
        given = None
    else:
        args, given = expr.of(Conditioned[Mul])
    
    bound_symbols = {x for x, *_ in limits}
    variable = []
    constant = []
    for arg in args:
        if any(any(V.index_contains(v) for V in bound_symbols) for v in arg.random_symbols):
            variable.append(arg)
        else:
            constant.append(arg)

    constant = Mul(*constant)
    variable = Mul(*variable)
    return Equal(self, constant * Expectation(variable, *limits, given=given))


@prove
def prove(Eq):
    from axiom import stats, algebra

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f, g = Function(real=True)
    a = Symbol(integer=True, random=True)
    b = Symbol(integer=True)
    Eq << apply(Expectation[a:θ](f(a) * g(b)))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.sum)

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.mul)



if __name__ == '__main__':
    run()
# created on 2023-03-24
