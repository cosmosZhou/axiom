from util import *


@apply
def apply(given):
    e, interval = given.of(Element)
    
    a, b = interval.args
    
    assert not interval.is_integer
        
    return Element(acos(e), interval.func(acos(b), acos(a), left_open=interval.right_open, right_open=interval.left_open))


@prove(proved=False)
def prove(Eq):
    x = Symbol(integer=True)
    a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))


if __name__ == '__main__':
    run()

