from util import *


@apply
def apply(self):
    args_lhs, args_rhs = self.of(Max + Max)
    
    args = []
    for lhs in args_lhs:
        for rhs in args_rhs:
            args.append(lhs + rhs)

    return Equal(self, Max(*args))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y, z, w = Symbol(real=True)
    Eq << apply(Add(Max(x, y), Max(z, w), evaluate=False))
    
    Eq << Eq[-1].this.lhs.apply(algebra.add.to.max)
    
    Eq << Eq[-1].this.lhs.find(Add[Max]).apply(algebra.add.to.max)
    
    Eq << Eq[-1].this.lhs.find(Add[Max]).apply(algebra.add.to.max)


if __name__ == '__main__':
    run()
# created on 2023-03-26
