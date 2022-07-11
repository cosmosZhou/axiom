from util import *


@apply
def apply(given, i=None):
    (x, w), y = given.of(Equal[MatMul])
    [n] = x.shape
    _i, _j = w.of(SwapMatrix)    
    assert _i >= 0 and _i < n
    assert _j >= 0 and _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')

    return Equal(Cup[i:n]({x[i]}), Cup[i:n]({y[i]}))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y))

    y_ = Symbol('y', Eq[0].lhs)
    Eq << discrete.cup.finiteset.matmul.apply(y_, Eq[1].lhs.variable, simplify=False).reversed

    Eq << y_.this.definition

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-3].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-10-31
