from util import *


@apply
def apply(el):
    i, (a, b) = el.of(Element[Range])
    a += 1
    b -= 1
    return Equal(Range(a, i) | Range(i + 1, b), Range(a, b) - {i})


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Element(i, Range(-1, n + 1)))

    Eq << sets.eq.of.et.infer.apply(Eq[1])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_union.then.ou), Eq[-1].this.rhs.apply(sets.el_union.of.ou)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_complement.of.et, simplify=False), Eq[-1].this.lhs.apply(sets.el_complement.then.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.to.et), Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.to.et), Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.to.et), Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.rhs.find(GreaterEqual).apply(algebra.ge.to.gt.strengthen)

    Eq << Eq[-2].this.find(NotElement).simplify()

    Eq << Eq[-1].this.find(Symbol >= Add).apply(algebra.ge.to.gt.strengthen)

    Eq << algebra.infer_ou.of.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer.of.et.infer.apply(Eq[-1]), algebra.infer.of.et.infer.apply(Eq[-2])

    Eq <<= algebra.infer_et.of.infer.delete.apply(Eq[-4]), algebra.infer_et.of.infer.delete.apply(Eq[-3]), algebra.infer_et.of.infer.delete.apply(Eq[-2], 0), algebra.infer_et.of.infer.delete.apply(Eq[-1], 0)

    Eq <<= algebra.infer.of.ou.apply(Eq[-4]), algebra.infer.of.ou.apply(Eq[-3]), algebra.infer.of.ou.apply(Eq[-2]), algebra.infer.of.ou.apply(Eq[-1])

    Eq <<= sets.ou.of.notin.range.apply(Eq[-2]), sets.ou.of.notin.range.apply(Eq[-1])

    Eq <<= sets.notin.of.is_empty.apply(Eq[-2]), sets.notin.of.is_empty.apply(Eq[-1])

    Eq << sets.el_range.then.et.apply(Eq[0])

    Eq << sets.ge.then.is_empty.range.apply(Eq[-2] + 1)

    Eq << algebra.lt.then.le.strengthen.apply(Eq[-1])

    Eq << sets.le.then.is_empty.range.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-28
# updated on 2023-05-20
