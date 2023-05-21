from util import *


def subs(eqs, index, reverse):
    eq = eqs[index]
    
    rhs = And(*eqs[:index], *eqs[index + 1:])

    old, new = eq.of(Equal)

    if reverse:
        old, new = new, old

    _rhs = rhs._subs(old, new)
    if _rhs != rhs:
        return _rhs


@apply
def apply(self, index=None, reverse=False):
    eqs = self.of(And)
    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Equal:
                if (rhs := subs(eqs, index, reverse)) is not None:
                    break
        else :
            return
    else:
        rhs = subs(eqs, index, reverse)
        eq = eqs[index]
    return eq, rhs


@prove
def prove(Eq):
    x, y = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(NotElement(f(x), S) & Equal(x, y))

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq <<= Eq[-1] & Eq[1]

    


if __name__ == '__main__':
    run()


# created on 2018-06-10
# updated on 2023-05-06
