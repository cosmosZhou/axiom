from util import *


@apply
def apply(self):
    arg = self.of(Re)
    if arg.is_Add:
        from axiom.algebra.add.to.mul import rewrite
        [*factors] = rewrite(arg)
    else:
        factors = arg.of(Mul)
        
    reals = []
    unreals = []
    for factor in factors:
        if factor.is_Mul:
            factors.extend(factor.args)
            continue
        
        if factor.is_super_real:
            reals.append(factor)
        else:
            unreals.append(factor)
    
    coeff = Mul(*reals)
    
    return Equal(self, coeff * Re(Mul(*unreals), evaluate=False))


@prove
def prove(Eq):
    from axiom import algebra

    c = Symbol(real=True)
    x, y = Symbol(complex=True)
    Eq << apply(Re(c * x + c * y, evaluate=False))

    Eq << Eq[-1].this.lhs.apply(algebra.re.to.add)

    Eq << Eq[-1].this.rhs.find(Re).apply(algebra.re.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    


if __name__ == '__main__':
    run()
# created on 2023-06-23
