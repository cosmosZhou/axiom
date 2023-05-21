from util import *


@apply
def apply(self, i=None):
    expr = self.of(ReducedSum)
    if i is None:
        i = expr.generate_var(integer=True, excludes={*expr.variables})
    
    n = expr.shape[-1]

    indices = (slice(None, None),) * (len(expr.shape) - 1) + (i,) if len(expr.shape) > 1 else i
    rhs = Sum[i:n](expr[indices])

    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True, given=False)
    y = Symbol(shape=(m, n), real=True)
    Eq << apply(ReducedSum(y))

    


if __name__ == '__main__':
    run()
# created on 2019-11-10
# updated on 2023-03-18
