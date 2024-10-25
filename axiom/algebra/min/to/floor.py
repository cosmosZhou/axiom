from util import *


@apply
def apply(self):
    args = self.of(Min)
    x = []
    for arg in args:
        if arg.is_Floor:
            arg = arg.arg
        elif arg.is_Add:
            flrs, non_flrs = std.array_split(arg.args, lambda arg : arg.is_Floor)

            assert flrs
            arg = Add(*non_flrs)
            assert arg.is_integer

            for f in flrs:
                arg += f.arg
        else:
            return
        x.append(arg)

    return Equal(self, Floor(Min(*x)))


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    n = Symbol(integer=True)

    Eq << apply(Min(n + floor(x), floor(y)))

    Eq << Eq[0].apply(algebra.eq.of.et.split.floor)

    assert n + floor(x) <= n + x

    Eq <<= algebra.then.lt.floor.apply(x) + n, algebra.then.lt.floor.apply(y)

    Eq << algebra.lt.lt.then.lt.min.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.add)

    Eq << Eq[-1] - 1

if __name__ == '__main__':
    run()
# created on 2020-01-25
