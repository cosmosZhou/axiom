from util import *



@apply
def apply(given):
    fn, *limits = given.of(All)
    return fn


@prove
def prove(Eq):
    from Axiom import Algebra

    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(All[e:S](f(e) > 0))

    Eq << Algebra.All.of.Or.apply(Eq[0])

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], index=0)




if __name__ == '__main__':
    run()

# created on 2018-12-13
# updated on 2023-05-20
from . import subs
