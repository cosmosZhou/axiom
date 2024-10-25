from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, q = is_imply_P.of(Assuming)
    _q, r = is_imply_Q.of(Assuming)
    if q != _q:
        p, q, S[q], r = _q, r, p, q

    return Assuming(p, r)


@prove
def prove(Eq):
    from axiom import algebra
    p, q, x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Assuming(p > q, x > y), Assuming(x > y, a > b))

    Eq << Eq[0].apply(algebra.assuming.then.ou)

    Eq << Eq[1].apply(algebra.assuming.then.ou)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << algebra.et.then.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.then.ou)

    Eq << Eq[2].apply(algebra.assuming.of.ou)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[-3]

    Eq << algebra.et.then.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-02
