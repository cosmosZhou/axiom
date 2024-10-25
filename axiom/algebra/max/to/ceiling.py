from util import *



@apply
def apply(self):
    args = self.of(Max)

    x = []
    for arg in args:
        if arg.is_Ceiling:
            x.append(arg.arg)
        elif arg.is_integer:
            x.append(arg)
        else:
            return

    return Equal(self, Ceiling(Max(*x)))


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    Eq << apply(Max(ceiling(x), ceiling(y)))

    Eq << Eq[0].apply(algebra.eq_ceiling.of.et)

    Eq <<= algebra.then.gt.ceiling.apply(x), algebra.then.gt.ceiling.apply(y)

    Eq << algebra.gt.gt.then.gt.max.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.add)

    Eq << Eq[-1] + 1

if __name__ == '__main__':
    run()
# created on 2020-01-24
