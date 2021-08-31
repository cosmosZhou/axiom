from util import *


@apply
def apply(given, S):
    A, B = given.of(Equal)
    return Equal(A | S, B | S)


@prove
def prove(Eq):
    A, B, S = Symbol(etype=dtype.integer)
    Eq << apply(Equal(A, B), S)
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

