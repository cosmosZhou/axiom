from util import *


@apply
def apply(self):
    args, *limits = self.of(Integral[Probability[Equal]])
    if args[-1].is_Tuple:
        (x, x_var), *weights = args
    else:
        x, x_var = args

    assert len(limits) == 1
    
    for S[x_var], *ab in limits:
        if ab:
            S[-oo], S[oo] = ab
            
        
    
    return Equal(self, 1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True, random=True)
    x_ = Symbol('x', real=True)
    Eq << apply(Integral[x_](Probability(x)))


if __name__ == '__main__':
    run()
from . import conditioned
# created on 2021-08-24
