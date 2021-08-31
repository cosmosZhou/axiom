from util import *


@apply
def apply(all_a, all_b):
    fn, *limits = all_a.of(All)
    _fn, *_limits = all_b.of(All)
    assert limits == _limits
    return All(fn & _fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(real=True)
    f, g, h = Function(integer=True)
    Eq << apply(All[e:g(e) > 0](f(e) > 0), All[e:g(e) > 0](h(e) > 0))

    Eq << algebra.all_et.imply.et.all.apply(Eq[-1])




if __name__ == '__main__':
    run()
