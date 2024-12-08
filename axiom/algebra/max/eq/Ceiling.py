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
    from Axiom import Algebra
    x, y = Symbol(real=True)
    Eq << apply(Max(ceiling(x), ceiling(y)))

    Eq << Eq[0].apply(Algebra.Eq_Ceiling.of.And)

    Eq <<= Algebra.Gt_Sub_.Ceiling.One.apply(x), Algebra.Gt_Sub_.Ceiling.One.apply(y)

    Eq << Algebra.Gt.Gt.to.Gt.Max.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Add)

    Eq << Eq[-1] + 1

if __name__ == '__main__':
    run()
# created on 2020-01-24
