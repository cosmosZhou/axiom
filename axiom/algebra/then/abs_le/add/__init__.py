from util import *


@apply
def apply(self):
    args = self.of(Add)
    assert not self.shape
    return LessEqual(abs(self), Add(*(abs(x) for x in args)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x + y)

    Eq << (Eq[0].lhs ** 2).this.expand()

    Eq << (Eq[0].rhs ** 2).this.expand()

    Eq << algebra.then.le.abs.apply(x * y)

    Eq << Eq[-1].this.rhs.apply(algebra.abs.to.mul)

    Eq << Eq[-1] * 2

    Eq << Eq[1] - Eq[2] + Eq[-1]

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)

    Eq << -Eq[-1]

    Eq << algebra.ge.then.ge.sqrt.apply(Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()

# created on 2019-07-25
# updated on 2023-06-03
from . import substract
