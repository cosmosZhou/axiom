from util import *


def absorb_back(Sum, Equal, cond, cond_sum, criteria=None):
    
    fb, gb = cond.of(Equal) 
    (fk, (k, a, b)), (gk, limit) = cond_sum.of(Equal[Sum[Tuple], Sum])
    
    assert k.is_integer
    assert limit == (k, a, b)
    
    assert fk._subs(k, b) == fb
    assert gk._subs(k, b) == gb

    if criteria:
        assert criteria(cond)
        assert criteria(cond_sum)

    return Equal(Sum[k:a:b + 1](fk), Sum[k:a:b + 1](gk))


@apply
def apply(*imply):
    return absorb_back(Sum, Equal, *imply)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(integer=True)
    f = Function.f(integer=True)
    Eq << apply(Equal(g(b), f(b)), Equal(Sum[k:a:b](g(k)), Sum[k:a:b](f(k))))

    Eq << algebra.eq.eq.imply.eq.add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(algebra.sum.to.add.split, cond={b})

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={b})


if __name__ == '__main__':
    run()

