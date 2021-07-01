from util import *


@apply
def apply(self):    
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    back = function._subs(i, b)
#     b >= a => b + 1 >= a
    return Equal(self, Sum[i:a:b + 1](function) - back, evaluate=False)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    f = Function.f(real=True)
    h = Function.h(real=True)
    
    Eq << apply(Sum[i:0:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Sum).split({n})

    
if __name__ == '__main__':
    run()
