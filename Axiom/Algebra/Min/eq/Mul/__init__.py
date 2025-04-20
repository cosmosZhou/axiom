from util import *


@apply
def apply(self, factor=None):
    args = self.of(Min)

    if factor is None:
        common_factors = None

        for arg in args:
            if not arg.is_Mul:
                return

            if common_factors is None:
                common_factors = {*arg.args}
            else:
                common_factors &= {*arg.args}

        if common_factors:
            factor = Mul(*common_factors)

    assert factor >= 0
    args = [arg / factor for arg in args]
    return Equal(self, factor * Min(*args))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True, positive=True)
    Eq << apply(Min(x * r, y * r))

    Eq << Eq[0].this.lhs.apply(Algebra.Min.eq.Ite)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Min.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.Mul)




if __name__ == '__main__':
    run()

# created on 2019-08-18
# updated on 2023-03-26
del Max
from . import Max
from . import of
