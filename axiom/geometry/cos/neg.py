from util import *


@apply
def apply(self):
    x = self.of(cos)
    if x.is_Mul:
        [*args] = x.args
        for i, arg in enumerate(args):
            if arg.is_Add:
                args[i] = -arg
                break
        else:
            return
        
        x = Mul(*args)
    else:
        x = -x
    
    return Equal(self, cos(x), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(complex=True)
    Eq << apply(cos(x - y))

    Eq << Eq[0].this.lhs.apply(geometry.cos.to.sub)

    Eq << Eq[-1].this.rhs.apply(geometry.cos.to.sub)

    
    


if __name__ == '__main__':
    run()
# created on 2023-05-20
# updated on 2023-06-02
