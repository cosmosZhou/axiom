from util import *


@apply
def apply(self):
    f, (x, (S[x], (S[x], (S[x], fx)))), *limits = self.of(Sum[Tuple[Cup[FiniteSet, Tuple[Equal]]]])

    f = f._subs(x, fx)
    return Equal(self, self.func(f, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)

    C = Symbol(etype=dtype.integer, given=True)

    f = Function(integer=True)
    h = Function(real=True)

    Eq << apply(Sum[j:conditionset(j, Equal(j, f(i))), i:C](h(i, j)))

    Eq << Sum[j:conditionset(j, Equal(j, f(i)))](h(i, j)).this.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, C))


if __name__ == '__main__':
    run()

# created on 2020-03-08
