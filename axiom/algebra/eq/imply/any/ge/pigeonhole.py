from util import *


@apply
def apply(eq):
    ((x, i), (S[i], S[0], k)), n = eq.of(Equal[Sum[Indexed]])
    return Exists[i:k](x[i] >= Ceiling(n / k))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(integer=True, nonnegative=True, shape=(oo,), given=True)
    n, k = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(Sum[i:k](x[i]), n))

    Eq << ~Eq[1]

    Eq << Eq[-1].this.expr.apply(algebra.lt.imply.le.strengthen)

    Eq << algebra.all_le.imply.le.sum.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] / k + 1

    Eq << ~Eq[-1].reversed

    

    Eq << algebra.imply.lt.ceiling.apply(n / k)

    


if __name__ == '__main__':
    run()
# created on 2022-07-06
