from util import *


@apply(simplify=None)
def apply(ne_zero):
    A = ne_zero.of(Unequal[Det, 0])
    return Unequal(Det(A.inverse()), 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    Eq << apply(Unequal(Det(A), 0))

    Eq << algebra.ne_zero.then.ne_zero.div.apply(Eq[0])

    Eq << Eq[1].this.lhs.apply(discrete.det.pow.to.pow, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-05-01
