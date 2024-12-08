from util import *



@apply
def apply(imply, index=None):
    eqs = imply.of(Or)
    if index is None:
        return eqs
    return eqs[index]


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True, given=True)

    f = Function(real=True, given=True)

    Eq << apply((f(y) > 0) | (f(x) > 0), index=0)

    Eq << ~Eq[0]

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=0)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-01-03
