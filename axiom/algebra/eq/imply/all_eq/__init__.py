from util import *


@apply
def apply(given, i=None):
    lhs, rhs = given.of(Equal)
    if i is None:
        if lhs.is_Lamda:
            i = lhs.variables[-1]
        elif rhs.is_Lamda:
            i = rhs.variable[-1]
        else:
            i = given.generate_var(integer=True)
            
    return All[i:lhs.shape[0]](Equal(lhs[i], rhs[i]))


@prove(provable=False)
def prove(Eq):
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Symbol(shape=(oo,), real=True)
    Eq << apply(Equal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    


if __name__ == '__main__':
    run()
# created on 2023-03-18


from . import limit_is_even
from . import limit_is_odd