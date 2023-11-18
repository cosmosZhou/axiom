from util import *


@apply
def apply(self, ahead=True):
    n = self.of(Factorial2)
    assert n.is_integer
    assert n >= 0
    return Equal(self, Factorial(n + 1) / Factorial2(n + 1) if ahead else Factorial(n) / Factorial2(n - 1))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Factorial2(n), False)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul.factorial2)

    # https://en.wikipedia.org/wiki/Double_factorial



if __name__ == '__main__':
    run()
# created on 2023-06-03
