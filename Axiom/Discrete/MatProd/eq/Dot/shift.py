from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(MatProduct)
    assert i.is_integer
    front = function._subs(i, a)
#     b >= a => b + 1 >= a
    assert a + 1 <= b
    return Equal(self, MatMul(front, MatProduct[i:a + 1:b](function)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Logic

    i = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(MatProduct[i:n + 1](f(i)))

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[0], cond=n > 0)

    Eq << Eq[2].this.lhs.apply(Algebra.Eq_0.of.Le_0)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])

    Eq << Logic.Imp.given.All.apply(Eq[1])

    n_ = Symbol('n', integer=True, positive=True)
    Eq << Algebra.All.given.Cond.subs.apply(Eq[-1], Eq[-1].variable, n_)

    Eq << Eq[-1].this.lhs.apply(Discrete.MatProd.eq.Dot.pop)
    Eq << Eq[-1].this.rhs.args[1].apply(Discrete.MatProd.eq.Dot.pop)


if __name__ == '__main__':
    run()
# created on 2020-11-16
