from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.pop import rewrite
    return Equal(self, rewrite(Inf, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    Eq << apply(Inf[i:n + 1](f(i)))

    
    Eq << Eq[-1].this.lhs.apply(algebra.inf.to.min.split, cond={n})
    


if __name__ == '__main__':
    run()
# created on 2023-04-23
