from util import *


@apply
def apply(self):
    function, *limits = self.of(Maxima)
    
    return Equal(self, -Minima(-function, *limits), evaluate=False)


@prove
def prove(Eq):
    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Maxima[x:a:b](f(x)))
    

    
    Eq << Eq[-1].this.find(Minima).simplify()


if __name__ == '__main__':
    run()
# created on 2021-09-30
# updated on 2021-09-30