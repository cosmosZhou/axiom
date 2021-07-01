from util import *


@apply
def apply(self):
    xi, limit = self.of(Sum)
    try:
        i, a, b = limit
    except:
        (i,) = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)
    
    diff = b - a
    assert diff == int(diff)
    
    sgm = ZeroMatrix(*xi.shape)
    for t in range(diff):
        sgm += xi._subs(i, a + t)
        
    return Equal(self, sgm)


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
     
    n = 5
    Eq << apply(Sum[i:n](x[i]))
    
    n -= 1
    Eq << Eq[-1].this.lhs.split({n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.split({n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.split({n})
    
    n -= 1
    Eq << Eq[-1].this.lhs.split({n})


if __name__ == '__main__':
    run()

from . import inner
from . import outer