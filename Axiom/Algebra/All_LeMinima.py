from util import *


@apply
def apply(self):
    function, *limits = self.of(Minima)
    return All(LessEqual(self, function), *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Minima[x:S](f(x)))

    y = Symbol(Eq[0].find(Minima))
    Eq << y.this.definition

    Eq << Algebra.Eq_Minima.to.All.Le.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

# created on 2019-09-17
