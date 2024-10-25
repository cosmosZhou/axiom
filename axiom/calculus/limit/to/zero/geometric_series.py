from util import *


@apply
def apply(self):
    (x, n), (S[n], S[oo]) = self.of(Limit[Pow])
    assert -1 < x < 1
    return Equal(self, ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    n = Symbol(integer=True)
    x = Symbol(domain=Interval(-1, 1, left_open=True, right_open=True))
    Eq << apply(Limit[n:oo](x ** n))

    Eq << Less(Abs(x), 1, plausible=True)

    Eq << algebra.abs_lt.of.et.apply(Eq[-1])

    Eq << calculus.abs_lt.then.is_zero.limit.geometric_series.apply(Eq[1], n)




if __name__ == '__main__':
    run()
# created on 2023-04-15
