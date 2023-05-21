from util import *

def process_slice(index, self_start, self_stop):
    start, stop = index.start, index.stop
    if start is None:
        start = self_start
    else:
        start = sympify(start)

    if stop is None:
        stop = self_stop
    else:
        stop = sympify(stop)

    if stop == self_stop:
        if start == self_start:
            return
        if start < 0:
            start = self_stop + start
        mid = start
    elif start == self_start:
        if stop < 0:
            stop = self_stop + stop
        mid = stop
    else:
        return start, stop

    return mid

def split(cls, self, indices, wrt=None, simplify=True, evaluate=False):
    function, *limits = self.of(cls)
    if len(limits) > 1:
        if wrt is None:
            x, *ab = limits[-1]
            if len(ab) == 2:
                a, b = ab
                universe = x.range(*ab)
                if x.is_integer:
                    if isinstance(indices, slice):
                        mid = process_slice(indices, a, b)
                        assert mid >= a, "mid >= a => %s" % (mid >= a)
                        assert mid <= b, "mid <= b => %s" % (mid <= b)

                        if mid is None:
                            return self
                        if isinstance(mid, tuple):
                            ...
                            assert False
                        return cls.operator(cls(function, *limits[:-1], (x, a, mid - 1)).simplify(), cls(function, *limits[:-1], (x, mid, b)).simplify(), evaluate=evaluate)
                    elif isinstance(indices, (set, Set)):
                        intersection = universe & indices
                        if intersection:
                            return cls.operator(cls(function, *limits[:-1], (x, intersection)).simplify(),
                                                      cls(function, *limits[:-1], (x, universe - indices)).simplify(), evaluate=evaluate)

            return self

        for i, limit in enumerate(limits):
            x, *ab = limit
            if x != wrt:
                continue
            if len(ab) == 2:
                universe = x.range(*ab)
            else:
                universe, *_ = ab

            limits1 = [*limits]
            limits1[i] = (x, universe & indices)

            limits2 = [*limits]
            limits2[i] = (x, universe - indices)

            return cls.operator(cls(function, *limits1).simplify(), cls(function, *limits2), evaluate=evaluate)
        return self

    (x, *ab), *_ = limits
    if x.is_Sliced:
        if not ab:
            x, z = x.bisect(indices, allow_empty=True).args
            return cls(cls(function, (x,)).simplify(), (z,))

    if not isinstance(indices, slice):
        if len(ab) == 1:
            universe = ab[0]
            if universe.is_bool:
                universe = x.domain_conditioned(universe)
        elif len(ab) == 2:
            a, b = ab
            if b.is_set:
                universe = conditionset(x, a, b)
            else:
                universe = x.range(*ab)
        else:
            universe = x.domain

        if not isinstance(indices, set) and indices.is_bool:
            indices = x.domain_conditioned(indices)
        intersection = universe & indices
        if intersection:
            first = cls(function, (x, intersection))
            second = cls(function, (x, universe - indices))

            if simplify:
                first = first.simplify()
                second = second.simplify()
            return cls.operator(first, second, evaluate=evaluate)
        return self

    if len(ab) == 2:
        a, b = ab
        if x.is_integer:
            mid = process_slice(indices, a, b)
            assert mid >= a, "mid >= a => %s" % (mid >= a)
            assert mid <= b, "mid <= b => %s" % (mid <= b)

            if mid is None:
                return self
            if isinstance(mid, tuple):
                ...
                assert False

            lhs = cls(function, (x, a, mid))
            rhs = cls(function, (x, mid, b))
            return cls.operator(lhs.simplify(), rhs.simplify(), evaluate=evaluate)

    return self


@apply
def apply(self, *, cond=None, wrt=None, evaluate=False):
    return Equal(self, split(Sum, self, cond, wrt=wrt), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Sum[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Element).apply(sets.el.to.ou.split, B)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.add)


if __name__ == '__main__':
    run()

# created on 2018-02-24
from . import limits
