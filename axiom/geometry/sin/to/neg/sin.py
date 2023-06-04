from util import *


@apply
def apply(self):
    x = self.of(sin)
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
    
    return Equal(self, -sin(x), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry
    
    x, y = Symbol(complex=True)
    Eq << apply(sin(x - y))
    
    Eq << Eq[0].this.lhs.apply(geometry.sin.to.sub)
    
    Eq << Eq[-1].this.rhs.find(Sin).apply(geometry.sin.to.sub)


if __name__ == '__main__':
    run()
# created on 2023-06-02
