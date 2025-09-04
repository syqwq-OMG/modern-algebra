#import "../template.typ": *

= 域论、线性空间
== 定义和例子
#definition([域])[
  假设集合 $F$ 有如下元素和定义在 $F$ 上的运算 :
  - *零元*: $0:=0_(F)$
  - *单位元*: $1:=1_(F)!=0_(F)$
  - *加法*: $+: F times F -> F, (x,y) |-> x+y$
  - *乘法*: $dot : F times F -> F, (x,y) |-> x dot y$
  并且， $F$ 上的加法和乘法满足：
  + *加法结合律*：$(x+y)+z=x+(y+z)$
  + *加法交换律*： $x+y=y+x$
  + *加法单位元*： $x+0=0+x=x$
  + *加法逆元*： $forall x in F, exists y in F, x+y=y+x=0$，记作 $-x$
  + *乘法结合律*： $x dot (y dot z)=(x dot y) dot z$
  + *乘法交换律*： $x dot y=y dot x$
  + *乘法单位元*： $x dot 1=1 dot x=x$
  + *乘法逆元*： $forall x in F^\* , exists y in F, x dot y=y dot x=1$，记作 $x^(-1)$
  + *分配律*：
    + $x dot (y+z)=x dot y+x dot z$
    + $(x+y) dot z = x dot z+y dot z$
]

#lemma([关于零元])[
  - $0 dot 0=0$
  - $forall x in F, x dot 0=0$
]

#proof[
  - 考虑如下事实：
  $
    a=0 dot (0+1) & =0 dot 1=0 \
                  & =0 dot 0+0 dot 1=0 dot 0+0=0 dot 0
  $
  - 考虑 $x dot 0=x dot (0+0)=x dot 0+x dot 0$ ，令 $y=-(x dot 0)$，得到
  $
    y+x dot 0=y+x dot 0+x dot 0 <=> 0=x dot 0
  $
]

注意到在定义中，我们要求 $0_(F)!=1_(F)$，若 $0=1$，则 $forall x in F, x=x dot 1=x dot 0=0$，于是 $F=\{ 0 \}$，太平凡了，于是我们排除这种情况。

又注意到，在乘法逆元定义中我们要求 $x !=0$，这是因为假设 $x=0$ 有乘法逆 $y$，则 $x dot y=y dot x=1 => 0 dot y=y dot 0=1 => 1=0$，则与上一条矛盾。

#remark([非零元记号])[
  为了方便讨论，我们将域中的非零元记作 $F^\*=F\\\{ 0 \}$
]

#remark([逆元是唯一的])[
  - 加法逆元是唯一的。假设 对于 $x$ 存在两个加法意义下的逆元 $y_1,y_2$，则
  $
    y_1=y_1+0=y_1+x+y_2=0+y_2=y_2
  $
  因此，$y_1=y_2$.

  - 乘法逆元是唯一的。证明类似，此处略。
]

#example([一些域的例子])[
  + $QQ, RR, CC$
  + $F=QQ(sqrt(2))=\{ x+sqrt(2)y mid(|) x,y in QQ \}$ \
    可以验证，每个元素确实存在加法逆元和乘法逆元（分母有理化）
  + $F=QQ(root(3, 2))$
]
#proof(name: [$F=QQ(root(3, 2))$ ])[
  记 $alpha=root(3, 2)$， $F=\{ x+y alpha + z alpha^(2) mid(|) x,y,z in QQ \}$ ，我们主要考虑乘法逆
  $
    frac(1, x+y alpha+z alpha^(2))&=frac(y-z alpha, (x+y alpha +z alpha^(2))(y-z alpha))
    = frac(*, x(y-z alpha)+alpha(y^(2) -z^(2) alpha^(2)))\
    &=A dot frac(1, s + t alpha)=frac(s^(2) -s t alpha + t^(2) alpha^(2), (s+t alpha)(s^(2) -s t alpha+t^(2) alpha^(2) ))\
    &=frac(*, s^(3) - t^(3) alpha^(3))=frac(*, s^(3) -2t^(3)) in F
  $
]

#remark([$F[x]$ 与 $F(x)$])[
  注意区分 $F[x]$ 和 $F(x)$，前者是 $lr({ sum_(i>=0) a_i x^(i) mid(|) a_i in F })$，后者是在域 $F$ 中添加 $x$ 生成的新的域。
]

#proposition([$QQ(alpha)$ 是域])[
  设 $alpha in CC$ 是 $f(x)$ 的根，其中 $f$ 是 $QQ$ 上的首一不可约多项式， $deg f=n$， 则有：
  $
    F=QQ(alpha)=\{ x_1+x_2 alpha+ dots.h.c +x_n alpha^(n-1) mid(|) x_i in QQ \}
  $
  $F$ 是一个域。
]<poly-f>
#proof()[
  我们主要考虑乘法逆。设
  $f(alpha) = alpha^(n)+b_1 alpha^(n-1) + dots.h.c + b_(n-1) alpha+b_(n)=0$
  ，对于形式更高阶的，可以通过带余除法，最终化成次数最高不超过 $n-1$ 的形式，因此我们考虑如下的乘法逆：
  $
    #let p = [$x_1+x_2 alpha+ dots.h.c +x_n alpha^(n-1)$]
    frac(1, g(alpha))=frac(1, #p)
  $
  首先我们有 $(f,g)=1$，于是 $exists u,v in QQ[alpha], u g+v f=1$，回到上面的式子
  $
    frac(1, g(alpha))=frac(u, u g + v f)(alpha)=u(alpha) in cal(P)_(n-1)(alpha)=F
  $
]

#example([在有理数域中加入两个无理数])[
  4. 考虑 $F=QQ(sqrt(2), sqrt(3))=\{ x_1+x_2 sqrt(2)+x_3 sqrt(3) +x_4 sqrt(6)
    mid(|) x_i in QQ\}$，也是域。
]
#proof()[
  首先，加法和乘法的封闭性容易验证。我们考虑乘法逆。
  #let p = [$x_1+x_2 sqrt(2)+x_3 sqrt(3) +x_4 sqrt(6)$]
  #let q = [$y_1+y_2 sqrt(2)+y_3 sqrt(3) +y_4 sqrt(6)$]
  $
    frac(1, #p) & =frac(#q, (#p)(#q))
  $
  因此，现在的核心任务就是考虑如何取 $y_i$ 的值，能够使得分母是一个有理数。我们将分母展开之后，进行待定系数，求解线性方程组即可。
  我们只需要无理数项的系数为0，因此只有三个方程，而有四个未知数，因此一定有非零解。
]

加了两个无理数，也确实构成一个域. 但是其实，加了这两个无理数和加一个无理数的效果是一样的。

我们来看看 $F'=QQ(sqrt(2)+sqrt(3))$。按照 @poly-f 的思路，
我们考虑能否找到一个多项式使得 $alpha=sqrt(2)+sqrt(3)$ 是他的根。通过平方，移项，平方，不难得到 $f(alpha)=alpha^(4)
-10 alpha^(2) +1=0$，利用 Eisenstein 判别法可以得到 $f$ 是一个不可约多项式，因此我们断言：
$
  F'=\{ x_1+x_2 alpha + x_3 alpha^(2) +x_4 alpha^(3) mid(|) x_i in QQ \}
$
接下来，我们要说明： $F=F'$。
手玩得到：
$
  cases(
    alpha^(3) & =11 & sqrt(2)+9 & sqrt(3) \
        alpha & =   &  sqrt(2)+ & sqrt(3)
  )
$
因此， $sqrt(2), sqrt(3)$ 都可以用 $alpha$ 的多项式表示出来，而他们又可以生成整个 $F$，因此整个 $F$ 都可以用 $F'$ 表示出来。
或者可以这样考虑 $F="span"(1,sqrt(2),sqrt(3),sqrt(6)), F'="span"(1,alpha,alpha^(2) ,alpha^(3),alpha^(4))$
，而我们的线性方程组又给出了这两组基之间的基变换，并且可以验证是双射，因此这两组基可以互相线性表出，从而他们张成的空间实际上是同一个空间。

我们把这种只加一个元的域扩张叫做*单扩张*，加若干元的扩张叫*有限扩张*。我们后面会看到，其实在一定条件下，有限域扩张就是单扩张。

#example([有限域的例子])[
  5. $FF_2=\{ overline(0), overline(1) \}$
  + $FF_3=\{ overline(0),overline(1), overline(2) \}$
]
#proof[
  通过列加法表、乘法表，不难验证他们都构成域。
]

#example([模素数剩余系构成的有限域])[
  7. 设 $p in NN inter PP$，则整数集的模 $p$ 剩余系： $FF_(p)=\{
    overline(0), overline(1), dots.h.c , overline(p-1) \}$ 是一个域。
]
#proof()[
  考虑乘法逆。对于 $overline(k) in FF_(p)^\*$，由于 $p in PP$，那么 $k bot p$，根据 Bezout 定理，我们有：
  $exists u,v in ZZ, u k + v p=1$ 两侧取模可得 $overline(u)$ 就是 $overline(k)$ 的乘法逆。

  *另解*。构造一个映射 $T:FF_(p)->FF_(p) , y |-> k y$，接下来，我们证明： $ker T=\{ 0 \}$。如果 $T(y)=0 <=>
  k y equiv 0 <=> k y = p m <=> p divides y <=> y=overline(0)$，因此， 我们可以把映射限制到 $FF_(p)^\*$ 上，为了证明每个元素
  都存在逆元，我们只需要证明 $T$ 是双射。由于 $T$ 是有限集合上的映射，因此只需要证明 $T$ 是单射即可。
  考虑 $T(y_1)=T(y_2)$，即 $k y_1=k y_2 <=> k(y_1-y_2) equiv 0 <=> y_1 equiv y_2$，因此 $T$ 是单射。
  从而，1 在 $T$ 的原像是唯一且存在的。
]

#remark()[
  若 $p in.not PP, m in NN, m>=2, ZZ_(m) = lr({ overline(0), overline(1), dots.h.c, overline(m-1) })$，则乘法逆不一定存在。比如 $m=4, 2 dot 2=0$，而 $overline(2)!=overline(0)$，此时我们称 $2$ 为零因子。
]

#example([函数域])[
  8. 设 $F$ 是一个域。 $F(x)=lr({ p(x)/q(x) mid(|) p(x), q(x) in F[x], q(x)!=0})$
  9. $K=CC(x, sqrt(x^(3) +2)) = CC(x)(y) tilde.op QQ(sqrt(2))=lr({ R_1(x)+R_2(x)y mid(|) R_1,R_2 in CC[x] ,y=sqrt(x^(3)+2)})$，此处类比向 $QQ$ 中加入 $sqrt(2)$. 这个 $K$ 是一条代数曲线上的亚纯函数。
]

#definition([线性空间])[
  设 $F$ 是一个域，集合 $V$ 和上面定义两个运算：
  - 加法： $+:V times V -> V$
  - 数乘： $dot :F times V -> V$
  如果 $0_(V) in N$，且满足：
  #let vv = eval(mode: "math", "0_V")
  + $(alpha+beta)+gamma=alpha+(beta+gamma)$
  + $alpha+beta=beta+alpha$
  + $alpha+vv=vv+alpha=alpha$
  + $forall alpha in V, exists bb(1) beta in V$ s.t. $alpha+beta=beta+alpha=vv$，且 $-alpha eq^(triangle.stroked.small) beta$
  + $(x y)alpha = x(y alpha)$
  + $1_(F) dot alpha = alpha$
  + $(x+y)alpha = x alpha + y alpha$
  + $x(alpha+beta)=x alpha + x beta$
  则称集合 $V$ 连同它上面的两个运算为 域 $F$ 上的*线性空间* $V$.
]
#example([线性空间的例子])[
  + $QQ(sqrt(2))$ 是 $QQ$ 上的2维线性空间。
  + $QQ(root(3, 2))$ 是 $QQ$ 上的3维空间。
  + $QQ(sqrt(2), sqrt(3))$ 是 $QQ$ 上的4维空间。
  + $F(x)$ 是无穷维的线性空间。
  + $K$ 是 $CC(x)$ 上的2维线性空间。
  + $RR$ 是 $QQ$ 上的无穷维空间。
  + $CC$ 是 $RR$ 上的2维空间。
]

通过类比 @poly-f ，我们来看一些更复杂的例子。

#theorem()[
  $p in PP, d in ZZ_(+)$，记 $q=p^(d)$，则存在一个 $q$ 元有限域 $FF_(q)$.
]
#proof()[
  还不会证明 #(eyes + drops + drops + drops)
]

#example([四元数])[
  10. 考虑四元数 $FF_4=lr({ x+y alpha mid(|) x,y in FF_2 })=FF_2(alpha)$ 的结构。
]
#solution()[
  $FF_2 = lr({ overline(0), overline(1) })$，为了方便研究，我们画出 $FF_2$ 的加法表和乘法表：
  #grid(
    columns: 5,
    h(1fr),
    symbol-table(r: 3, c: 3)([$+$], [0], [1], [0], [0], [1], [1], [1], [0]),
    h(1fr),
    symbol-table(r: 3, c: 3)([$dot$], [0], [1], [0], [0], [0], [1], [0], [1]),
    h(1fr)
  )
  考虑 $FF_2[x]: f(x)=x^(2)+p x+q$ 中的不可约多项式，其中 $p, q in FF_2 $。
  
  首先，$f(x) in lr({ x^(2) , x^(2) +x,x^(2) +1,x^(2) +x+1 })$，其中的不可约多项式实际上只有 $x^(2) +x+1$. 因此若 $FF_4=FF_2(alpha)$，则 $alpha$ 满足 $alpha^(2) +alpha+1=0 <=> alpha^(2) =1+alpha$。 此时， $FF_4=lr({ 0,1,alpha, 1+alpha=alpha^(2)  })$. 接下来我们可以验证这样的 $FF_4$ 是否是域。利用加法表和乘法表：
  #let a=[$alpha$]
  #let aa=[$alpha^(2)$]
  #grid(
    columns: 5,
    h(1fr),
    align: horizon,
    symbol-table(r: 5, c: 5)(align: bottom,
      [$+$], [$0$], [$1$], a,aa,
    [$0$], [$0$], [$1$], a,aa,
    [$1$], [$1$], [$0$],aa,a,
    a,a,aa,[$0$],[$1$],
    aa,aa,a,[$1$],[$0$]
    ),
    h(1fr),
    symbol-table(r: 5, c: 5)(align: bottom,
      [$dot$], [$0$], [$1$], a,aa,
    [$0$], [$0$], [$0$], [$0$],[$0$],
    [$1$], [$0$], [$1$],a,aa,
    a,[$0$],a,aa,[$1$],
    aa,[$0$],aa,[$1$],a
    ),h(1fr))
    发现乘法逆其实是 $alpha^(-1)=alpha^(2) $。因此这确实是一个域。
]

类似的，我们还可以找到一些比较简单的可以手玩的例子。

#example()[
  11. $FF_9=FF_3(alpha)$，其中 $alpha^(2) =2$ 或 $alpha^(2) +1=0$.
  + $FF_8=FF_2(alpha)$，其中 $alpha^(3)=1+alpha$.
]


== 域的同态
#definition([线性空间的同态])[
  设 $V_1, V_2$ 是域 $F$ 上的线性空间，若映射 $phi : V_1 -> V_2$ 满足：
  + $phi(alpha+beta)=phi(alpha)+phi(beta)$
  + $phi(k alpha)=k phi(alpha)$
  则称 $phi$ 是*同态*。
]

其实，同态就是保运算的映射。

#definition([域的同态])[
  设 $F_1,F_2$ 是两个域。 若 $phi:F_1 -> F_2$ 满足：
  + $phi(0_(F_1))=0_(F_2)$
  + $phi(1_(F_1))=1_(F_2)$
  + $phi(x+y)=phi(x)+phi(y)$
  + $phi(x y)=phi(x) phi(y)$
  则称 $phi$ 是*同态*。
]

若 $phi$ 是同态，有以下事实：
+ $phi(-x)=-phi(x)$
+ $phi(x^(-1))=phi(x)^(-1)$

#theorem([域同态是单射])[
  若 $phi:F_1 -> F_2$ 是域同态，则 $phi$ 是单射。
]
#proof()[
  假设 $phi(x_1)=phi(x_2), x=x_2-x_1$，则
  $
    phi(x)=phi(x_1)-phi(x_2)=0
  $
  若 $x!=0$，则存在 $x^(-1)$，于是
  $
    "LHS" & =phi(x)dot phi(x^(-1))=1 \
    "RHS" & =0 dot phi(x^(-1))=0
  $
  而 $0!=1$，因此 $forall x_1!=x_2, phi(x_1)!=phi(x_2)$.
]

#definition([子域、域扩张])[
  若 $F$ 是域， $E$ 是 $F$ 的子集，若满足：
  + $0_(F) in E$
  + $1_(F) in E$
  + $forall x,y in E , x+y in E, x y in E$
  + $forall x in E, -x in E$
  + $x in E without lr({ 0 }), x^(-1)in E$
  则称 $E$ 为 $F$ 的*子域*， $F$ 为 $E$ 的一个*扩域*。 记作 $F \/ E$.
]

#remark()[
  若存在 $phi:F_1 -> F_2$，则 $F_2$ 可以称为 $F_1$ 的子域。
]

#let phiff = eval(mode: "math", "phi:F_1 -> F_2")

#definition([域的同构])[
  若 #phiff 是域的同态，若 $phi$ 是满射，则称 $phi$ 是*同构*。\
  特别的，如果 $F_1=F_2$，则称 $phi$ 是 $F$ 的*自同构*。
]

#example([子域的例子])[
  + $RR \/ QQ$
  + $CC \/ RR$
  + $QQ(sqrt(2))\/ QQ$
  + $QQ(sqrt(2), sqrt(3)) \/ QQ(sqrt(2))$
  + $QQ(sqrt(2), sqrt(3)) tilde.equiv QQ(sqrt(2)+sqrt(3))$
  + $FF_(4) \/ FF_2$
]

#definition([不动域])[
  设 $sigma:F -> F$是 $F$ 的自同构，则 $E=lr({ x in F mid(|) sigma(x)=x })$ 是一个子域，叫做 $sigma$ 的*不动域*。
]

#example([自同构的例子])[
  #let b = text(baseline: -0.5em)[$-$]
  设 $#b:CC -> CC, x+y i |-> x-y i$，可以验证满足：
  + $overline(0)=0$
  + $overline(1)=1$
  + $overline(z_1+z_2)=overline(z_1)+overline(z_2)$
  + $overline(z_1 z_2)=overline(z_1) dot overline(z_2)$
  则 $#b$ 的不动域为 $z=overline(z) => RR$.
]
#example([另一个例子])[
  定义 $sigma: QQ(sqrt(2)) -> QQ(sqrt(2)), x+sqrt(2)y |-> x-sqrt(2)$ 也是自同构。
]
#proof()[
  设 $z_1=x_1+sqrt(2)y_1, z_2=x_2+sqrt(2)y_2$，容易验证他满足域同构的所有要求。考虑他的不动域： $z=sigma(z) => x+sqrt(2)y=x-sqrt(2)y => z in QQ$.
]

#problem([二次域之间的关系])[
  $QQ(sqrt(2))$ 和 $QQ(sqrt(3))$ 有什么关系？
]
#solution()[
  没什么关系。不存在同态 $phi:QQ(sqrt(2)) -> QQ(sqrt(3))$. 若有同态 $phi$，令 $a=phi(sqrt(2))=x+sqrt(3)y$，则 $a^(2) =phi(sqrt(2))^(2) =phi(2)=phi(1)+phi(1)=2$，所以有 $(x+sqrt(3)y)^(2) =2 => x,y in emptyset$.
]

\ 可见不同的二次域之间没啥关系。

#theorem([域与线性空间])[
  若 $F\/E$，则 $F$ 是 $E$ 的线性空间. 我们记 $[F:E]=dim_(E)(F)$ 为 $F$ 作为 $E$ 的线性空间的维数，称为 $F \/ E$ 的*次数*。  
]
#proof()[
  这很显然。
]

#proposition()[
  $QQ$ 没有真子域. 
]
#proof()[
  设 $E subset.eq QQ$，且 $1 in E, 0 in E$。若 $E$ 为子域，那么：
  - 加法封闭： $NN subset.eq E$
  - 加法有逆： $ZZ subset.eq E$
  - 乘法有逆： $QQ subset.eq E$
  因此，$E=QQ$.     
]

#proposition()[
  $FF_(q)$ 没有真子域，其中 $p in PP$. 
]
#proof()[
  设 $FF_(p)\/E$，于是有 $\#E, \#FF_(p) < oo$，因为 $FF_(p)$ 可以看成是 $E$ 上的线性空间，考虑一组基和任意 $x in FF_(p)$ 在这个基下的坐标，可以得到 $\#FF_(p)=(\#E)^(d)$，其中 $d=[F:E]$。又 $p in PP$，我们得到 $d=1, \#E=\#FF_(p)$，因此 $E=FF_(p) $.          
]

#definition([有限扩张])[
  若 $[F:E]<oo$，则称 $F\/E$ 是*有限扩张*。  
]

#remark([$E$-代数])[
  111
]

== 域的特征 (characteristic)
#definition([域的特征])[
  $F$ 是域。定义映射 $N:NN -> F, n |->n_(F)$，即
  $
  cases(
    N(0_(NN) )&=0_(F),
    N(n+1) &=N(n)+1_(F) 
  )
  $  
  若 $N$ 为单射，则称 $F$ 的特征为0，记作 $char F=0$.\
  若 $N$ 不是单射，则存在一个最小的 $p in NN^\*$ s.t. $N(p)=0$，此时 $char F=p$.   
]

















































#pagebreak()
