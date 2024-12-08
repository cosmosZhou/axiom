from util import *


@apply
def apply(A, B):
    return Equal(A, Union(A & B, A - B, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    C = Symbol(A - B)
    Eq << C.this.definition

    Eq << Sets.Eq.to.Eq.Union.apply(Eq[1], A & B)

    Eq << Eq[0].subs(Eq[1].reversed).reversed


if __name__ == '__main__':
    run()
# created on 2020-10-05
