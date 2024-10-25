# 什么是axiom.top  
  <br>

[axiom.top](../index.php)是一个基于数学定理知识库、用于证明数学命题的网站，此[github工程](https://github.com/cosmosZhou/axiom)目前有两种语言的版本，Pythony语言版本的定理库主要依靠开源符号计算项目 
[sympy](https://github.com/sympy/sympy) 改写, 其中函数命名主要参考数学软件语言
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer), Lean版本的定理库由Python版本翻译而来。 
其主要特征在于：半机械化、公理化、严密的推理逻辑。  
基本设计理念是：语法精确，表达简洁，执行高效，书写美观。
	
	
* 所述半机械化，是指目前做不到全自动根据数学命题题设直接打印出证明过程，而是需要人脑的辅助，人必须通过检索定理库，告诉计算机，面对什么样的题型使用什么样的定理；全机械化，自动化的符号推理算法尚未有可演示的研究成果；
* 所述公理化，是指所有已证明的数学定理，归根结底是通过有限个公理经过有限次逻辑运算推导出来的，而公理是不需要证明的，其真伪是人为假定成立的，整个数学定理库就是建立在公理的假设之上展开构建的；当然根据哥德尔不完备性定理（Goedel Incompleteness Theorem），任何一个自洽的推理系统，必然存在不能证明，亦不能证伪的命题，此类命题不能通过有限个公理经过有限次逻辑运算（布尔运算）导出；
* 所述严密的推理逻辑，就是依据[希尔伯特纲领](https://en.wikipedia.org/wiki/Hilbert%27s_program)中的申明，在论证过程中，以[形式语言](https://en.wikipedia.org/wiki/Formal_language)的既定逻辑来引导程序进行推理，力求确保计算结果在[形式语言](https://en.wikipedia.org/wiki/Formal_language)的既定语法规则内有效，且所有推理都依据某个公理或者定理进行。在本系统中，所有数学命题都将被[Python](https://www.python.org/)或[Lean](https://lean-lang.org/)语句精确描述出来，不存在自然语言描述数学问题时存在的歧义性(显然，同理，一般地，以此类推，反之亦然，综上所述等证明用语)，也不存在浮点数引起的误差问题。  

我们可以在Google搜索引擎中定位到网站信息：[定理库](https://www.google.com.hk/search?q=%E5%AE%9A%E7%90%86%E5%BA%93)。  
目前开源社区中其它定理库包括：[leanprover](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html)、[coq](https://github.com/coq/coq)和[isabelle](https://isabelle.in.tum.de/)


若要熟练掌握定理推导系统，需要掌握6种推理方法为：  
1，归纳法  
归纳法(induction)就是数学归纳法，其本质就是从特殊到一般的推理过程  
2，演绎法  
演绎法(deduction)是归纳法的逆运算，其本质就是从一般到特殊的推理过程  
3，类比法  
类比法(analogy)就是从已知的特殊到未知的特殊的推理方法，该方法没有严格的数学理论支撑  
4，反证法  
反证法(contradiction)是假设命题为假，尝试是否能推导出一个假命题的推理过程  
5，分治法  
分治法(divide & conquer)就是分类讨论法，将一个复杂的问题拆解为若干简单问题的推理过程  
6，溯因法  
溯因法(abduction)是一种已知结果倒推可能原因的推理方法
<br><br>
------


# 数学定理库的建设
  <br>
  
目前积累了<label id=count>____</label>个已知数学定理用于交互式半机械化数学推导。涉及：	
	
* [algebra](../?module=algebra) 初等代数，主要涉及等式的恒等、换元变换、有限级数[∑裂项求和](../?module=algebra.sum.to.add.telescope)、∏裂项求积技巧，[一元一次方程](../?module=algebra.poly_is_zero.then.et.infer.simple_equation)，[一元二次方程](../?module=algebra.poly_is_zero.then.et.infer.quadratic)，[一元三次方程](../?module=algebra.poly_is_zero.then.et.infer.cubic)，[一元四次方程](../?module=algebra.poly_is_zero.then.et.infer.quartic)的求解问题，[分部求和](../?module=algebra.sum.to.add.by_parts)定理；
[数学归纳法](../?module=algebra.ne_zero.infer.then.ne_zero.induct)的证明；
* [sets](../?module=sets) 集合论, 即sets theory，集合论是整个数学分析、数学推导系统的理论核心；比如
[容斥原理](../?module=sets/eq/principle/inclusion_exclusion/basic)的证明。
* [geometry](../?module=geometry) 几何学，包含不少三角函数恒等式，比如
[和差化积](../?module=geometry.cos.to.add.principle)，[积化和差](../?module=geometry.mul.to.add.sin)，等等。
* [calculus](../?module=calculus) 微积分，主要包含以下内容： 
[极限定义](../?module=calculus/eq/to/any_all/limit_definition) 及其理论；[无穷级数](../?module=calculus.eq.then.eq.series.infinite.coefficient) 的运算性质；
[分部积分](../?module=calculus.integral.to.add.by_parts) 定理；
* [discrete](../?module=discrete) 数论，离散数学，组合数学，线性代数，[第二类Stirling数](../?module=discrete.stirling2.to.add.recurrence)的组合学推导，
[Catalan数](../?module=discrete.eq.eq.then.eq.catalan.recurrence)的推导，[连分数](../?module=discrete.add.to.pow.HK.recurrence)初步理论；[Cholesky矩阵分解](../?module=discrete.eq_adjoint.infer_gt_zero.then.any.eq.Cholesky)存在定理。
* [stats](../?module=stats) 概率统计学，比如[Bayes公式](../?module=stats.prob.to.div.prob.bayes)，[大数定理](../?module=stats.eq_conditioned.eq_expect.eq_var.then.eq.limit.prob.law_of_large_numbers)；
* [keras](../?module=keras) 机器学习，深度学习中的数学模型，
[LSTM](../?module=keras.eq.eq.then.eq.long_short_term_memory)，
[GRU](../?module=keras.eq.gated_recurrent_unit)，
[CNN](../?module=keras.eq_lamda_bool.then.eq.conv1d)，
[BERT](../?module=keras.matmul_softmax.to.lamda.div.scaled_dot_product_attention)，
[GPT](../?module=keras.matmul_softmax.to.lamda.matmul.gpt)，
条件自由场[CRF](../?module=keras.ne_zero.eq.eq.eq.then.et.crf)，KMeans
[聚类收敛性](../?module=sets.el.notin.le.then.le.st.variance)、用于Vision Transformer的[广义旋转位置编码](../?module=keras.eq_mul.eq_mul.eq_block.then.eq.matmul.softmax.to.lamda.sum.plane)、强化学习的[策略梯度定理](../?module=keras.eq_conditioned.eq_expect.is_finite.is_finite.then.eq.matmul.grad.expect.unbiased_advantage_estimate)的推导及证明。  

<br><br>
-------
该公理化半机械化数学证明工具可以简化论证过程，实现“给思考加上发动机”，研究者只需掌握论证的宏观脉络，具体计算交付给计算机即可。主要可以用于理论性数学证明，对数学学院的学生，算法工程师、研究员在算法研究，数学分析过程中有一定参考价值，
也可以用于数学工作者整理数学定理知识，无需手动编辑繁琐的数学公式，无需手动进行纸笔演算，通过在线IDE,就可以对定理过程进行编辑，从而完成数学定理的整理工作。其中在线IDE提供F3快捷键可以方便定位任意定理，函数，符号的定义，
对于研究和教学都有化繁为简的实用价值，是一本用Python语言编写的数学教材，电子版的数学、算法参考书。
<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	$('#count').innerHTML = await get("/axiom/php/request/count.php");
</script>