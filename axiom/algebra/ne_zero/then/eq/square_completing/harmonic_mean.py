from util import *


@apply
def apply(ne_zero, self):
    a, b = ne_zero.of(Unequal[Add, 0])
    (S[a], (x, y)), (S[b], (S[x], z)) = self.of(Expr * (Expr - Expr) ** 2 + Expr * (Expr - Expr) ** 2)
    return Equal(self, (a + b) * (x - (a * y + b * z) / (a + b)) ** 2 + a * b / (a + b) * (y - z) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y, z = Symbol(complex=True)
    Eq << apply(Unequal(a + b, 0), a * (x - y) ** 2 + b * (x - z) ** 2)

    Eq << algebra.ne_zero.then.eq.square_completing.apply(Eq[0], Eq[1].lhs, x)

    Eq << Eq[-1].this.find(Add * (~Add) ** 2).args[1].apply(algebra.div.cancel, S(1) / 2)

    Eq << Eq[-1].this.find(Add * (~Add) ** 2).args[1].apply(algebra.mul.negate)

    Eq << algebra.eq.then.eq.transport.apply(Eq[-1], rhs=2)

    Eq << Eq[-1].this.rhs.find(Add[Mul, Mul, Mul]).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Mul[Add[-Pow, -Pow]]).apply(algebra.mul.negate)

    Eq << Eq[-1].this.find(Pow + Pow).args[:3].apply(algebra.poly.square_completing, y)

    Eq << Eq[-1].this.find(Pow + Pow).apply(algebra.poly.square_completing, y)

    Eq << Eq[-1].this.rhs.find(Add[Pow]).apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.rhs.find(Add[Add * Pow]).apply(algebra.add.to.mul)

    Eq << algebra.eq.then.eq.transport.apply(Eq[-1], lhs=2)

    # https://en.wikipedia.org/wiki/Normal_distribution# Scalar_form



if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-20
