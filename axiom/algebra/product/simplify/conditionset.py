from util import *


@apply
def apply(self):
    function, (x, (__x, (_x, (___x, fx)))), *limits = self.of(Sum[Tuple[Cup[FiniteSet, Tuple[Equal]]]])
    assert x == _x == __x == ___x
    
    function = function._subs(x, fx)
    return Equal(self, self.func(function, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    C = Symbol.C(etype=dtype.integer, given=True)

    f = Function.f(integer=True)
    h = Function.h(real=True)

    Eq << apply(Sum[j:conditionset(j, Equal(j, f(i))), i:C](h(i, j)))

    Eq << Sum[j:conditionset(j, Equal(j, f(i)))](h(i, j)).this.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, C))


if __name__ == '__main__':
    run()
