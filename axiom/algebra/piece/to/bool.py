from util import *


@apply
def apply(self):
    (one, cond), (zero, S[True]) = self.of(Piecewise)
    if zero:
        S[0], S[1] = one, zero
        cond = cond.invert()
    else:
        S[0], S[1] = zero, one

    return Equal(self, Bool(cond))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Piecewise((0, x > y), (1, True)))

    Eq << Eq[0].this.rhs.apply(algebra.bool.to.piece)

    

    


if __name__ == '__main__':
    run()
# created on 2021-12-16
# updated on 2023-05-15
