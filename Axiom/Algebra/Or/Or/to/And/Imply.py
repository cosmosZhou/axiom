from util import *


@apply
def apply(ou, ou_f):
    p0, p1 = ou.of(Not | Not)
    (p0, q0), (p1, q1) = ou_f.of(And | And)
    return Imply(p0, q0), Imply(p1, q1)


@prove
def prove(Eq):
    from Axiom import Algebra

    p0, q0, p1, q1 = Symbol(bool=True)
    Eq << apply(Not(p0) | Not(p1), p0 & q0 | p1 & q1)

    Eq << Algebra.Imply.of.Or.apply(Eq[2])

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq[-1].this.apply(Algebra.And.equ.Or)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Algebra.Imply.of.Or.apply(Eq[3])

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq[-1].this.apply(Algebra.And.equ.Or)

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2022-04-01
