from util import *


@apply
def apply(self):
    x = self.of(Floor)
    n = x.generate_var(integer=True, var='n')
    return Equal(self, Maxima[n:n<=x](n))


@prove(provable=False)
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(Floor(x))

    #Eq << Eq[0].reversed + 1 - Floor(x)
    #Eq << Eq[-1].this.lhs.apply(algebra.add.to.frac)


if __name__ == '__main__':
    run()

# created on 2021-08-15
