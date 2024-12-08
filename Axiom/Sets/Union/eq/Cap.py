from util import *



@apply
def apply(self):
    for i, union in enumerate(self.args):
        if isinstance(union, Cap):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            function = union.expr | this
            return Equal(self, union.func(function, *union.limits), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets
    x = Symbol(etype=dtype.integer)
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cap[k:n](f(k)) | x)

    Eq << Sets.Eq.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Cap.of.All_In),\
    Eq[-1].this.lhs.apply(Sets.In_Cap.to.All_In)

    Eq <<= Eq[-2].this.rhs.expr.apply(Sets.In_Union.of.Or),\
    Eq[-1].this.lhs.expr.apply(Sets.In_Union.to.Or)

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Union.to.Or),\
    Eq[-1].this.rhs.apply(Sets.In_Union.of.Or)

    Eq <<= Eq[-2].this.find(Element[Cap]).apply(Sets.In_Cap.to.All_In),\
    Eq[-1].this.find(Element[Cap]).apply(Sets.In_Cap.of.All_In)

if __name__ == '__main__':
    run()
# created on 2021-07-11
