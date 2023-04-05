from util import *


@apply
def apply(self, i=0, j=1):
    assert i < j

    [function, *limits] = self.of(Integral)
    i_limit, j_limit = self.limits[i], self.limits[j]

    assert not i_limit._has(j_limit[0])
    limits[i], limits[j] = limits[j], limits[i]

    return Equal(self, Integral(function, *limits))


@prove(provable=False)
def prove(Eq):
    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b, y:c:d](f(x) * g(x, y)))

    


if __name__ == '__main__':
    run()
# created on 2023-03-20
