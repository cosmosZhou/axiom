from util import *


@apply
def apply(self, index=-1):
    x, y = std.array_split(self.of(Sin[Add]), index)
    x, y = Add(*x), Add(*y)
    return Equal(sin(x + y), sin(x) * cos(y) + cos(x) * sin(y))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x + y))

    Eq << geometry.cos.to.sub.apply(cos(x + y))

    Eq << Eq[-1].subs(x, x + S.Pi / 2)

    Eq << -Eq[-1]

    
    


if __name__ == '__main__':
    run()

# created on 2020-11-24

from . import expi
# updated on 2023-11-26
