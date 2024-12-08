from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    x, p = is_imply_P.of(Imply)
    y, q = is_imply_Q.of(Imply)

    return Imply(x & y, p & q)


@prove
def prove(Eq):
    from Axiom import Algebra

    p0, p1, q0, q1 = Symbol(bool=True)
    Eq << apply(Imply(p0, q0), Imply(p1, q1))

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Imply(p0 & p1, p0, plausible=True), Imply(p0 & p1, p1, plausible=True)

    Eq <<= Algebra.Imply.Imply.to.Imply.trans.apply(Eq[0], Eq[-2]), Algebra.Imply.Imply.to.Imply.trans.apply(Eq[1], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-02-02
# updated on 2022-01-27
