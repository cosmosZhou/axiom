from util import *


@apply
def apply(eq_R, t):
    (cos, sin, S[-sin], S[cos]), Rk = eq_R.of(Equal[Matrix])
    sin = -sin
    k = sin.of(Sin)
    S[k] = cos.of(Cos)
    return Equal(Rk.subs(k, t).T @ Rk, Rk.subs(k, k - t))

@prove
def prove(Eq):
    from axiom import geometry, algebra

    # R denotes rotary matrix
    R = Function(shape=(2, 2), real=True)
    # k, t denote token index
    k, t = Symbol(integer=True)
    Eq << apply(Equal(R(k), [
            [cos(k), -sin(k)],
            [sin(k), cos(k)]]), t)

    Eq << Eq[0].subs(k, t).T @ Eq[0]

    Eq <<= Eq[-1].rhs.find(Sin * Sin + Cos * Cos).this.apply(geometry.add.to.cos),\
        Eq[-1].rhs.find(Sin * Cos - Sin * Cos).this.apply(geometry.sub.to.sin)

    Eq << -Eq[-1]

    Eq << Eq[-1].find(-~Sin).this.apply(geometry.sin.to.neg.sin)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[0].subs(k, k - t)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-09-16
