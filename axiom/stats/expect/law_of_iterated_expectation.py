from util import *


@apply
def apply(self, *vars):
    given = S.true
    for v in vars:
        given &= v.surrogate
        
    expr, *limits = self.args
    
    vars_given = set()
    for x in expr.random_symbols:
        for v in vars:
            if v.index_contains(x):
                vars_given.add(x)
    
    from std import deleteIndices
    deleteIndices(limits, lambda limit: limit[0] in vars_given)
    rhs = Expectation(Expectation(expr | given, *limits))
    assert rhs.random_symbols == self.random_symbols
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import stats

    #this is the proof of the law of iterated expectations
    #https://en.wikipedia.org/wiki/Law_of_total_expectation
    x, y, z = Symbol(real=True, random=True)
    f = Function(real=True, shape=())
    Eq << apply(Expectation(f(x)), y, z)

    Eq << Eq[-1].this.rhs.apply(stats.expect.law_of_total_expectation)

    #https://spinningup.openai.com/en/latest/spinningup/extra_pg_proof2.html
    


if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-04
