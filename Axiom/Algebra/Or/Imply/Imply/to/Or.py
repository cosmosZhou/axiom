from util import *


@apply
def apply(ou, inter0, inter1):
    p0, p1 = ou.of(Or)
    S[p0], q0 = inter0.of(Imply)
    S[p1], q1 = inter1.of(Imply)

    return p0 & q0 | p1 & q1


@prove
def prove(Eq):
    from Axiom import Algebra

    p0, q0, p1, q1 = Symbol(bool=True)
    Eq << apply(p0 | p1, p0 >> q0, p1 >> q1)

    Eq << ~Eq[-1]

    Eq << Algebra.Imply.to.Or.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(Algebra.And.equ.Or)

    Eq << Eq[-1].this.args[1].apply(Algebra.And.equ.Or)

    Eq << Algebra.Imply.to.Or.apply(Eq[2])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(Algebra.And.equ.Or)

    Eq << Eq[-1].this.args[1].apply(Algebra.And.equ.Or)

    Eq << ~Eq[-1]





if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-05-20