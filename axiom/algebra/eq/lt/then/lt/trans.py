from util import *


@apply
def apply(eq, cond):
    from axiom.algebra.eq.gt.then.gt.trans import trans
    return trans(Less, eq, cond)
    

@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)
    Eq << apply(Equal(a, x), x < b)

    Eq << Eq[2].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-11-12
