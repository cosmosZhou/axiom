from util import *


@apply
def apply(self):
    x, y = self.of(Sin[Add])
    return Equal(sin(x + y), sin(x) * cos(y) + cos(x) * sin(y))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x + y))

    Eq << geometry.cos.to.sub.apply(cos(x + y))

    # x = Add(*x)
    Eq << Eq[-1].subs(x, x + S.Pi / 2)
    Eq << -Eq[-1]


if __name__ == '__main__':
    run()

# created on 2020-11-24

from . import expi
