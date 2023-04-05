from util import *


@apply
def apply(self, *indices):
    if len(indices) == 1:
        i = 0
        j, = indices
    else:
        i, j = indices

    expr, *limits = self.of(Expectation)
    x, = limits[i]

    size = x.shape[0]

    if isinstance(j, slice):
        _start, _stop = j.start, j.stop
        assert _stop <= size and _start < size
    else:
        assert 0 <= j < size
    limits[i] = (x[x.index_complement(x[j])],)
    return Equal(self, Expectation(Expectation(expr | Equal(x[j], x[j].surrogate), *limits), (x[j],)))


@prove
def prove(Eq):
    from axiom import algebra, stats, calculus

    #this is the proof of the law of iterated expectations
    #https://en.wikipedia.org/wiki/Law_of_total_expectation
    n = Symbol(domain=Range(2, oo))
    i = Symbol(domain=Range(1, n))
    x = Symbol(real=True, shape=(oo,), random=True)
    f = Function(real=True, shape=())
    Eq << apply(Expectation(f(x[:n])), slice(0, i))

    Eq << Eq[-1].this.rhs.find(f[~Sliced]).apply(algebra.expr.to.block.split, i)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.to.integral)

    

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.mul.bayes)

    Eq << Eq[-1].this.find(And).apply(algebra.et_eq.to.eq.concat)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.concat)

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(f[~Sliced]).apply(algebra.expr.to.block.split, i)

    #https://spinningup.openai.com/en/latest/spinningup/extra_pg_proof2.html
    


if __name__ == '__main__':
    run()
# created on 2023-03-31
# updated on 2023-04-01
