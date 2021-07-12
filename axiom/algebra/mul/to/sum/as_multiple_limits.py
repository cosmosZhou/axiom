from util import *


@apply
def apply(self): 
    (fi, (i, *iab)), (fj, (j, *jab)) = self.of(Sum * Sum)
    if i == j:
        _j = self.generate_var(excludes=i, integer=True)
        fj = fj._subs(j, _j)
        j = _j

    rhs = Sum((fi * fj).powsimp(), (i, *iab), (j, *jab))
    return Equal(self, rhs, evaluate=False)



@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Sum[i:m](f(i)) * Sum[i:n](g(i)))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()