from util import *


def rewrite(Sum, self, simplify=True):
    (expr, *limits_e), *limits_s = self.of(Sum[Expectation])
    
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    expr = Sum(expr, *limits_s)
    if simplify:
        expr = expr.simplify()
    return Expectation(expr, given=given)

@apply
def apply(self, *, simplify=True):
    return Equal(self, rewrite(Sum, self, simplify))


@prove
def prove(Eq):
    from axiom import stats

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    s = Symbol(real=True, random=True)
    Eq << apply(Sum[k:n](Expectation(f(x[k]) | s)))

    Eq << Eq[-1].this.rhs.apply(stats.expect_sum.to.sum.expect)

    


if __name__ == '__main__':
    run()
# created on 2023-04-02
