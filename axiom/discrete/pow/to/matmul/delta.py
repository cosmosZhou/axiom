from util import *


@apply
def apply(self, upper=1):
    z, n = self.of(Pow)
    assert n.is_integer
    assert upper >= 0
    assert n >= 0
    i = self.generate_var(integer=True)
    return Equal(self, Lamda[i:n + upper](z ** i) @ Lamda[i:n + upper](KroneckerDelta(i, n)))


@prove
def prove(Eq):
    from axiom import discrete

    h = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    z = Symbol(real=True)
    Eq << apply(z ** n)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)
    


if __name__ == '__main__':
    run()
# created on 2023-08-26
