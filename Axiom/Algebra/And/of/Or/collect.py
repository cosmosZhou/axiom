from util import *


@apply
def apply(self, *, cond=None):
    cond=sympify(cond)

    matched = []
    unmatch = []
    for eq in self.of(And):
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert not unmatch
    return Or(cond, And(*matched))


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q, r, s = Symbol(bool=True)
    Eq << apply(And(q | p, r | p, s | p), cond=p)

    Eq << Algebra.Or.to.And.apply(Eq[1], None)

    Eq << Algebra.And.of.And.apply(Eq[0], None)




if __name__ == '__main__':
    run()
# created on 2022-01-28
# updated on 2023-05-21