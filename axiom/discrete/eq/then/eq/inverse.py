from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.shape
    assert lhs.is_invertible or rhs.is_invertible
    return Equal(lhs.inverse(), rhs.inverse())


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    B = Symbol(real=True, shape=(n, n), singular=False)
    Eq << apply(Equal(A, B))

    Eq << Eq[-1].subs(Eq[0])



    Eq << discrete.eq.then.eq.det.apply(Eq[0])
    Eq << Unequal(Det(B), 0, plausible=True)

    Eq << algebra.eq.ne.then.ne.trans.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-02-11
