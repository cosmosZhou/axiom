from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b, d= domain.of(Range)
    assert x.is_integer
    return And(x >= a, x < b, Equal(x % d, a % d))

@prove(provable=False)
def prove(Eq):
    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b, d)))

    

    

    


if __name__ == '__main__':
    run()
# created on 2022-01-01
