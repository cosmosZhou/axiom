from util import *



@apply
def apply(cond, ou):
    cond = cond.invert()
    for i, c in enumerate(ou.of(Or)):
        if c == cond:
            conds = [*ou.args]
            del conds[i]
            return Or(*conds)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Element(x, S), NotElement(x, S) | (f(x) > g(x)))

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.et.imply.et.apply(Eq[-1])

    
    


if __name__ == '__main__':
    run()

# created on 2018-01-23
# updated on 2021-11-20