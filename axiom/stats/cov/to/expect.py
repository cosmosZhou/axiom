from util import *


@apply
def apply(self):
    (fx, fy), *limits = self.of(Covariance)
    return Equal(self,
                 Expectation((fx - Expectation(fx, *limits)) * (fy - Expectation(fy, *limits)), *limits))

@prove(provable=False)
def prove(Eq):
    x, y = Symbol(integer=True, random=True)
    Eq << apply(Covariance[x, y](x, y))


if __name__ == '__main__':
    run()
# created on 2023-03-24
