from util import *


def rewrite(self):
    expr, (i, *_), (j, *_) = self.of(Sum)
    assert i.type == j.type
    z = Dummy('z', **i.type.dict)
    this = self.limits_subs(i, z)
    this = this.limits_subs(j, i)
    this = this.limits_subs(z, j)
    return this

@apply
def apply(self):
    return Equal(self, rewrite(self))


@prove
def prove(Eq):
    i, j, k = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    g = Symbol(shape=(oo, oo), real=True)
    h = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:f(j), j:A](h[i] * g[i, j]))

    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    
    


if __name__ == '__main__':
    run()

# created on 2019-11-08
# updated on 2023-05-02
