from util import *


@apply
def apply(self):
    a, b = self.of(Interval)
    return Subset(self, self.copy(stop=abs(b)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(Interval(x, y, right_open=True))

    Eq << algebra.then.le.abs.apply(y)

    Eq << sets.le.then.subset.interval.lower.apply(Eq[1], x, right_open=True)


if __name__ == '__main__':
    run()
# created on 2019-07-09
