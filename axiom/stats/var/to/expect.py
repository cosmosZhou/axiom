from util import *


@apply
def apply(self):
    fx, *limits = self.of(Variance)
    return Equal(self,
                 Expectation((fx - Expectation(fx, *limits)) ** 2, *limits))

@prove(provable=False)
def prove(Eq):
    x = Symbol(integer=True, random=True)
    Eq << apply(Variance[x](x))

    


if __name__ == '__main__':
    run()
# created on 2023-03-24
