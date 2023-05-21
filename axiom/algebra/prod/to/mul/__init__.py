from util import *


@apply
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    return Equal(self, associate(Product, self, simplify=simplify))


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(Product[i:n](f(i) * h(i)))


if __name__ == '__main__':
    run()

from . import split
from . import doit
# created on 2018-04-14
from . import shift
from . import pop
from . import unshift
from . import push
