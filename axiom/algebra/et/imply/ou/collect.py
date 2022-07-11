from util import *



@apply
def apply(self, *, cond=None):
    cond=sympify(cond)

    matched = []
    unmatch = []
    for eq in self.args:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert not unmatch
    return Or(cond, self.func(*matched))


@prove
def prove(Eq):
    from axiom import algebra

    p, q, r, s = Symbol(bool=True)
    Eq << apply(And(q | p, r | p, s | p), cond=p)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    


if __name__ == '__main__':
    run()

# created on 2019-05-05
# updated on 2022-01-28
