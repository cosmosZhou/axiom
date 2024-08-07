from util import *


def rewrite(cls, self):
    x = self.of(cls)
    if x.is_Mul:
        [*args] = x.args
        for i, arg in enumerate(args):
            if arg.is_Add:
                args[i] = -arg
                break
        else:
            args.append(S.NegativeOne)
        
        x = Mul(*args)
    else:
        x = -x
    return cls(x)

@apply
def apply(self):
    return Equal(self, rewrite(Abs, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(abs(x - y))

    Eq << Eq[0].this.lhs.apply(algebra.abs.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.abs.to.piece.le_zero)

    Eq << -Eq[-1].this.find(LessEqual)

    
    


if __name__ == '__main__':
    run()
# created on 2018-01-19
# updated on 2023-11-26
