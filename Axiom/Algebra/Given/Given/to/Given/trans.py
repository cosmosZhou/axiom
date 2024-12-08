from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, q = is_imply_P.of(Given)
    _q, r = is_imply_Q.of(Given)
    if q != _q:
        p, q, S[q], r = _q, r, p, q

    return Given(p, r)


@prove
def prove(Eq):
    from Axiom import Algebra
    p, q, x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Given(p > q, x > y), Given(x > y, a > b))

    Eq << Eq[0].apply(Algebra.Given.to.Or)

    Eq << Eq[1].apply(Algebra.Given.to.Or)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Algebra.And.to.Or.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(Algebra.And.to.Or)

    Eq << Eq[2].apply(Algebra.Given.of.Or)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Algebra.And.to.Or.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-02
