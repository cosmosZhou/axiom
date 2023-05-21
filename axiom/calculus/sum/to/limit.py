from util import *


@apply
def apply(self, var=None):
    expr, *limits, (n, S[0], S[oo]) = self.of(Sum)
    if var is None:
        var = n
        
    return Equal(self, Limit[var:oo](Sum[n:var](expr, *limits)), evaluate=False)


@prove
def prove(Eq):
    from axiom import calculus

    n = Symbol(integer=True)
    s = Function(real=True)
    Eq << apply(Sum[n:oo](s(n)))

    Eq << Eq[0].this.rhs.apply(calculus.limit.to.sum)

    


if __name__ == '__main__':
    run()
# created on 2023-04-16
