from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y):
    assert not x.shape and not y.shape
    return LessEqual(abs(x), abs(x - y) + abs(y))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x, y)

    Eq << algebra.imply.add_ge.abs.apply(Eq[0].rhs).reversed

    
    


if __name__ == '__main__':
    run()

# created on 2019-07-26
# updated on 2023-06-03
