from std.file import createNewFile
import std
from os.path import dirname, basename, abspath, sep
import re

workingDirectory = dirname(dirname(__file__)) + '/'

def get_args_for_writing(module):
    prove = [{"py":"Eq.induct = keras.ne_zero.eq.eq.eq.eq.imply.eq.policy_gradient.induct.apply(*Eq[:4], n)","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {{\\color{green} {γ}}^{n} \\int \\nabla_{θ} V^\\pi_{θ}({s}_{n}) \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1} + \\sum\\limits_{k:n}{\\color{green} {γ}}^{k} \\int \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sum_{{a}_{k}} \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) Q^\\pi_{θ}({s}_{k}, {a}_{k})\\, d{s}_{1:k + 1}}\\tag*{Eq.induct}\\]"},{"py":"Eq << calculus.eq.imply.eq.limit.apply(Eq.induct, (n, oo))","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\lim\\limits_{n \\to \\infty}\\left({\\color{green} {γ}}^{n} \\int \\nabla_{θ} V^\\pi_{θ}({s}_{n}) \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1} + \\sum\\limits_{k:n}{\\color{green} {γ}}^{k} \\int \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sum_{{a}_{k}} \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) Q^\\pi_{θ}({s}_{k}, {a}_{k})\\, d{s}_{1:k + 1}\\right)}\\tag*{Eq[5]}\\]"},{"py":"Eq.limit = Eq[-1].this.find(Limit).apply(calculus.limit.to.add)","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\lim\\limits_{n \\to \\infty} {\\color{green} {γ}}^{n} \\int \\nabla_{θ} V^\\pi_{θ}({s}_{n}) \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1} + \\lim\\limits_{n \\to \\infty} \\sum\\limits_{k:n}{\\color{green} {γ}}^{k} \\int \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sum_{{a}_{k}} \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) Q^\\pi_{θ}({s}_{k}, {a}_{k})\\, d{s}_{1:k + 1}}\\tag*{Eq.limit}\\]"},{"py":"Eq << algebra.imply.all.le_sup.apply(Eq[4].find(Sup))","latex":"\\[\\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{t})}\\right| \\leq \\sup\\limits_{{s}_{t}} \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{t})}\\right|\\tag*{Eq[6]}\\]"},{"py":"Eq << algebra.le.imply.le.mul.apply(Eq[-1].subs(t, n), Eq[-2].find(Product))","latex":"\\[\\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right| \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\leq \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sup\\limits_{{s}_{n}} \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right|\\tag*{Eq[7]}\\]"},{"py":"Eq << calculus.le.imply.le.integral.apply(Eq[-1], (s[1:n + 1].var,))","latex":"\\[\\int \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right| \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1} \\leq \\left(\\int \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1}\\right) \\sup\\limits_{{s}_{n}} \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right|\\tag*{Eq[8]}\\]"},{"py":"Eq << Eq[-1].this.find(Integral[Product]).apply(stats.integral_prod.to.one)","latex":"\\[\\int \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right| \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1} \\leq \\sup\\limits_{{s}_{n}} \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right|\\tag*{Eq[9]}\\]"},{"py":"Eq << Eq[4].this.lhs.limits_subs(s[t].var, s[n].var)","latex":"\\[\\sup\\limits_{{s}_{n}} \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right| < \\infty\\tag*{Eq[4]}\\]"},{"py":"Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[4])","latex":"\\[\\int \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right| \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1} < \\infty\\tag*{Eq[10]}\\]"},{"py":"Eq << calculus.imply.abs_le.integral.apply(Eq.induct.find(Integral))","latex":"\\[\\left|{\\int \\nabla_{θ} V^\\pi_{θ}({s}_{n}) \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1}}\\right| \\leq \\int \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{n})}\\right| \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1}\\tag*{Eq[11]}\\]"},{"py":"Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[-2])","latex":"\\[\\left|{\\int \\nabla_{θ} V^\\pi_{θ}({s}_{n}) \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1}}\\right| < \\infty\\tag*{Eq[12]}\\]"},{"py":"Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)","latex":"\\[\\left|{{\\color{green} {γ}}}\\right| < 1\\tag*{Eq[13]}\\]"},{"py":"Eq << Eq[-1].this.lhs.doit()","latex":"\\[\\text{True}\\]"},{"py":"Eq << calculus.lt.is_finite.imply.is_zero.limit.apply(Eq[-2], Eq[-1], n)","latex":"\\[{\\lim\\limits_{n \\to \\infty} {\\color{green} {γ}}^{n} \\int \\nabla_{θ} V^\\pi_{θ}({s}_{n}) \\prod\\limits_{t:n}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:n + 1}} = {\\mathbf{0}}\\tag*{Eq[14]}\\]"},{"py":"Eq << Eq.limit.subs(Eq[-1])","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\lim\\limits_{n \\to \\infty} \\sum\\limits_{k:n}{\\color{green} {γ}}^{k} \\int \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sum_{{a}_{k}} \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) Q^\\pi_{θ}({s}_{k}, {a}_{k})\\, d{s}_{1:k + 1}}\\tag*{Eq[15]}\\]"},{"py":"Eq << Eq[-1].this.rhs.apply(calculus.limit.to.sum)","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\sum\\limits_{k=0}^{\\infty} {\\color{green} {γ}}^{k} \\int \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sum_{{a}_{k}} \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) Q^\\pi_{θ}({s}_{k}, {a}_{k})\\, d{s}_{1:k + 1}}\\tag*{Eq[16]}\\]"},{"py":"Eq << Eq[-1].this.find(Derivative[Probability]).apply(calculus.grad.to.mul.grad.log)","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\sum_{k} {\\color{green} {γ}}^{k} \\int \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right) \\cdot \\sum_{{a}_{k}} \\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) Q^\\pi_{θ}({s}_{k}, {a}_{k})\\, d{s}_{1:k + 1}}\\tag*{Eq[17]}\\]"},{"py":"Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.expect)","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\sum_{k} {\\color{green} {γ}}^{k} \\int \\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:k + 1}}\\tag*{Eq[18]}\\]"},{"py":"Eq << Eq.hypothesis.find(Expectation).this.apply(stats.expect.conditioned.importance_sampling, θ)","latex":"\\[{\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} = {\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}\\tag*{Eq[19]}\\]"},{"py":"Eq << Eq[-1].this.rhs.find(Derivative[Probability]).apply(calculus.grad.to.mul.grad.log)","latex":"\\[{\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} = {\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}\\tag*{Eq[20]}\\]"},{"py":"Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)","latex":"\\[{\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} = {\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - \\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} V^\\pi_{θ}({s}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}\\tag*{Eq[21]}\\]"},{"py":"Eq << Eq[-1].this.rhs.apply(stats.expect.to.add)","latex":"\\[{\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} = {\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) + \\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(- \\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} V^\\pi_{θ}({s}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}\\tag*{Eq[22]}\\]"},{"py":"Eq << Eq[-1].this.find(Expectation[Conditioned[Mul[NegativeOne]]]).apply(stats.expect.to.mul)","latex":"\\[{\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} = {\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) - V^\\pi_{θ}({s}_{k}) \\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}\\tag*{Eq[23]}\\]"},{"py":"Eq << Eq[-1].this.find(Mul[~Expectation[Conditioned[Derivative]]]).apply(stats.expect_conditioned.to.zero.st.grad.log.prob)","latex":"\\[{\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} = {\\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}\\tag*{Eq[24]}\\]"},{"py":"Eq << Eq.hypothesis.subs(Eq[-1])","latex":"\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\sum_{k} {\\color{green} {γ}}^{k} \\int \\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ} \\left(\\nabla_{θ} \\log {\\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:k + 1}}\\tag*{Eq[18]}\\]"}]
    given = {"py":"b, D = Symbol(integer=True, positive=True)\ns = Symbol(shape=(oo, b), real=True, random=True) #states \/ observation\n\na = Symbol(shape=(oo,), integer=True, random=True) #actions\nr = Symbol(shape=(oo,), real=True, random=True) #rewards\nθ, θ_quote = Symbol(shape=(D,), real=True) #trainable weights for the agent\nt, k = Symbol(integer=True) #time step counter\nV = Function(r'V^\\pi', real=True, shape=()) #State-Value Function\nQ = Function(r'Q^\\pi', real=True, shape=()) #Action-Value Function\nγ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1\nG = Lamda[t](Sum[k:0:oo](γ ** k * r[t + k + 1])) #sum of discounted future reward\nn = Symbol(integer=True, positive=True, given=False)\n*Eq[-5:], Eq.hypothesis = apply(Unequal(Probability[a:θ](s, a), 0),\n            Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #history-irrelevant conditional independence assumption for rewards based on states and actions\n            Equal((Q[π] ^ γ)(s[t].var, a[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t] & a[t])),\n            Equal((V[π] ^ γ)(s[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t])),\n            Less(Sup[s[t].var](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo, evaluate=False),\n            n, θ_quote)","latex":"\\[\\mathbb{p}_{θ}\\left({\\color{red} {a}}\\wedge {\\color{red} {s}}\\right) \\neq 0\\tag*{Eq[0]}\\]\\[{{{\\color{red} {r}}}_{t + 2:} \\mathrel{\\bigg|} {{\\color{red} {a}}}_{t}\\wedge {{\\color{red} {s}}}_{t}} = {{{\\color{red} {r}}}_{t + 2:}}\\tag*{Eq[1]}\\]\\[{Q^\\pi_{θ}({s}_{t}, {a}_{t})} = {\\mathop{\\mathbb{E}}\\limits_{\\begin{subarray}{c}{{\\color{red} {r}}}_{t + 1:}\\\\{\\color{red} {a}} \\sim θ\\end{subarray}} \\left(\\sum\\limits_{k=0}^{\\infty} {\\color{green} {γ}}^{k} {{\\color{red} {r}}}_{k + t + 1} \\mathrel{\\bigg|} {{\\color{red} {a}}}_{t}\\wedge {{\\color{red} {s}}}_{t}\\right)}\\tag*{Eq[2]}\\]\\[{V^\\pi_{θ}({s}_{t})} = {\\mathop{\\mathbb{E}}\\limits_{\\begin{subarray}{c}{{\\color{red} {r}}}_{t + 1:}\\\\{\\color{red} {a}} \\sim θ\\end{subarray}} \\left(\\sum\\limits_{k=0}^{\\infty} {\\color{green} {γ}}^{k} {{\\color{red} {r}}}_{k + t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)}\\tag*{Eq[3]}\\]\\[\\sup\\limits_{{s}_{t}} \\left|{\\nabla_{θ} V^\\pi_{θ}({s}_{t})}\\right| < \\infty\\tag*{Eq[4]}\\]"}
    imply = "\\[{\\nabla_{θ} V^\\pi_{θ}({s}_{0})} = {\\sum_{k} {\\color{green} {γ}}^{k} \\int \\mathop{\\mathbb{E}}\\limits_{{\\color{red} {a}} \\sim θ'} \\left(\\frac{\\left(Q^\\pi_{θ}({s}_{k}, {{\\color{red} {a}}}_{k}) - V^\\pi_{θ}({s}_{k})\\right) \\nabla_{θ} \\mathbb{P}_{θ}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)}{\\mathbb{P}_{θ'}\\left({{\\color{red} {a}}}_{k} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right)} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{k}\\right) \\prod\\limits_{t:k}\\mathbb{p}\\left({{\\color{red} {s}}}_{t + 1} \\mathrel{\\bigg|} {{\\color{red} {s}}}_{t}\\right)\\, d{s}_{1:k + 1}}\\tag*{Eq.hypothesis}\\]"
    unused = ["#https:\/\/spinningup.openai.com\/en\/latest\/spinningup\/rl_intro.html#bellman-equations\n#http:\/\/incompleteideas.net\/book\/bookdraft2017nov5.pdf (Page 47)\n#https:\/\/lilianweng.github.io\/posts\/2018-04-08-policy-gradient\/\n#https:\/\/danieltakeshi.github.io\/2017\/04\/02\/notes-on-the-generalized-advantage-estimation-paper\/\n#https:\/\/spinningup.openai.com\/en\/latest\/spinningup\/rl_intro.html#id4\n#https:\/\/huggingface.co\/deep-rl-course\/unit4\/pg-theorem?fw=pt\n#https:\/\/www.youtube.com\/watch?v=cQfOQcpYRzE\n#https:\/\/www.52coding.com.cn\/tags\/Reinforcement-Learning\/\n#TRPO\n#https:\/\/arxiv.org\/pdf\/1502.05477.pdf\n\n"]
    createdTime = '2023-03-30'
    updatedTime = '2023-04-03'
    
    imply = imply.replace('\\', '\\\\')
    return module, prove, given, imply, unused, createdTime, updatedTime

class LocalJsWriter:
    def __init__(self):
        ...
        
    def url_address(self, package):
        return f"{dirname(dirname(__file__))}/target/{package.replace('.', '/')}.html"

    def select_axiom_lapse_from_axiom(self):
        return {}

    def load_data(self, table, data, **kwargs):
        from _collections import defaultdict
        state_count_pairs = defaultdict(int)
        repertoire = defaultdict(dict)
        total = 0
        
        targetFiles = []

        for file in std.listdir(workingDirectory + 'static/components', 'vue'):
            generate_js(file)
            targetFiles.append('vue/' + basename(file))
        
#         parentPath = workingDirectory + 'static/'
#         for file in std.listdir(workingDirectory + 'static/codemirror', 'js', recursive=True):
#             generate_js(file, None, abspath(file)[len(parentPath):-3].split(sep))
#             targetFiles.append(abspath(file)[len(parentPath):])
            
        for package, module, state, lapse, latex in data:
            state_count_pairs[state.name] += 1
            total += 1
            
            if state.name != 'proved':
                section = module.split('.', 1)[0]
                section = repertoire[section]
                if not state.name in section:
                    section[state.name] = []
                section[state.name].append(module)
                
            write_html(module, generate_theorem(*get_args_for_writing(module)), targetFiles)
            
        state_count_pairs['total'] = total
        state_count_pairs = [dict(state=state, count=count) for state, count in state_count_pairs.items()]
        write_js_object('target/js/axiomSummary.js', '', state_count_pairs=state_count_pairs, repertoire=repertoire)
    
instance = LocalJsWriter()
            
def write_js_object(path, namespace, **kwargs):
    
    texts = []
    for attr, value in kwargs.items():
        value = std.json_encode(value)
        if namespace:
            text = 'window.%s.%s = %s;' % (namespace, attr, value)
        else:
            text = 'window.%s = %s;' % (attr, value)
            
        texts.append(text)

    file = workingDirectory + path
    createNewFile(file)
    # Text(file).write('')
    with open(file, 'w', encoding='utf8') as file:
        for text in texts:
            print(text, file=file)


def generate_js(file, transform=None, attributes=None):
    name = basename(file)
    name, ext = std.split_filename(name)    
    with open(file, 'r', encoding='utf8') as file:
        text = file.read()
        if transform:
            text = transform(name, text)

        text = text.replace('\\', '\\\\')
        text = text.replace('`', "\`")
        text = text.replace('${', "\${")
        
        if attributes:
            window = 'window.js'
            previousAssignments = []
            for attr in attributes[:-1]:
                attr = re.sub('\W', '_', attr)
                previousAssignments.append(f'if (!{window}.{attr}) {window}.{attr} = {{}};\n')
                window += "." + attr

            previousAssignments = ''.join(previousAssignments)
            assert '-' not in previousAssignments
            lastAttribute = re.sub('\W', '_', attributes[-1])
            text = previousAssignments + f"{window}.{lastAttribute} = `{text}`;"
            mjs = 'target/%s.js' % '/'.join(attributes)
        else:
            text = f'window.{ext}.{name} = `{text};`'
            mjs = 'target/%s/%s.%s' % (ext, name, ext)

    file = workingDirectory + mjs
    createNewFile(file)
    # Text(file).write('')
    with open(file, 'w', encoding='utf8') as file:
        print(text, file=file)

    return mjs
    
def write_html(module, textContent, targetFiles):
    parentPath = '../' * len(module.split('.'))
    textContent = textContent % '\n'.join([f"<script src='{parentPath}target/{mjs}'></script>" for mjs in targetFiles])        

    mjs = 'target/%s.html' % module.replace('.', '/')
    file = workingDirectory + mjs
    createNewFile(file)
    # Text(file).write('')
    with open(file, 'w', encoding='utf8') as file:
        print(textContent, file=file)

    return mjs
    
        
def generate_theorem(module, prove, given, imply, unused, createdTime, updatedTime):
    parentPath = '../' * len(module.split('.'))
    return f"""
<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="{parentPath}static/css/style.css">
<link rel="shortcut icon" type="image/x-icon" href="{parentPath}static/favicon.ico">
<title>{module}</title>
<link rel=stylesheet href="{parentPath}static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="{parentPath}static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="{parentPath}static/codemirror/addon/hint/show-hint.css">
<style>
div {{
    caret-color: transparent;
}}
</style>
<body></body>

<script>
MathJax = {{
    startup: {{
        ready(){{
              console.log('MathJax is loaded, but not yet initialized');
              MathJax.startup.defaultReady();
              console.log('MathJax is initialized, and the initial typeset is queued');
              
              MathJax.startup.promise.then(() => {{
                  console.log('MathJax initial typesetting complete');
                  setTimeout(() => {{
                      var p = document.querySelectorAll('p');
                      if (p.length) {{
                          for (let p of document.querySelectorAll('p')){{
                              if (p.innerText.startsWith("\\\\[")) {{
                                  console.log("unfinished work detected!");
                                  console.log(p.innerText);
                                  console.log('trying MathJax.typesetPromise() again;');
                                  MathJax.typesetPromise();
                                  break;
                              }}
                          }}
                      }}
                      else {{
                          console.log("no p tags have been detected!");
                          setTimeout(() => {{
                              console.log("MathJax.typesetPromise() due to absence of p tags");
                              MathJax.typesetPromise();
                          }}, 1000);
                      }}
                  }}, 1000);
              }});                  
         }}
      }},

    tex: {{
        maxBuffer: 60 * 1024,       // maximum size for the internal TeX string (10K)
        //reference: http://docs.mathjax.org/en/latest/options/input/tex.html?highlight=MAXBUFFER#the-configuration-block
    }},
}};
</script>

<script async src="{parentPath}static/unpkg.com/mathjax@3.2.0/es5/tex-chtml.js"></script>
<script src="{parentPath}static/unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="{parentPath}static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="{parentPath}static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="{parentPath}static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src='{parentPath}static/js/std.js'></script>
<script src='{parentPath}static/js/utility.js'></script>
<script>
window.vue = {{}};
window.js = {{}};
</script>
%s

<script type=module>
//import * as codemirror from "{parentPath}static/codemirror/lib/codemirror.js";
//import * as python from "{parentPath}static/codemirror/mode/python/python.js";
//import * as active_line from "{parentPath}static/codemirror/addon/selection/active-line.js";
//import * as show_hint from "{parentPath}static/codemirror/addon/hint/show-hint.js";
//import * as matchbrackets from "{parentPath}static/codemirror/addon/edit/matchbrackets.js";

var logs = [];

var error = [];
//console.log(logs);
for (let i = 0; i < logs.length; ++i){{
    var log = logs[i];
    if (log.startsWith('{{') && log.endsWith('}}')){{
        error.push(JSON.parse(log));
        logs.delete(i);
        break;
    }}
    
    if (log.startsWith('[') && log.endsWith(']')){{
        logs.delete(i);
        error = JSON.parse(log);
        break;
    }}
}}

createApp('render', {{
    error : [],
    logs : [],
    prove : {prove},
    unused : {unused},
    module: "{module}",
    given: {given},
    imply: `{imply}`,
    where: "",
    createdTime: `{createdTime}`,
    updatedTime: `{updatedTime}`,
}});

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>"""

    
if __name__ == '__main__':
    ...