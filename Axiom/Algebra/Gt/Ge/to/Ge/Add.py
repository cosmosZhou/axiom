from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Greater)
    b, y = x_less_than_b.of(GreaterEqual)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    from Axiom import Algebra
    a, x, b, y = Symbol(real=True)

    Eq << apply(a > x, y >= b)

    Eq << Algebra.Gt.Ge.to.Gt.Add.apply(Eq[0], Eq[1])

    Eq << Algebra.Gt.to.Ge.relax.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2019-07-12