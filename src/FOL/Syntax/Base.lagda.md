---
url: fol.syntax.base
---

# 一阶逻辑 ▸ 语法 ▸ 语法蕴含

本篇引入一阶逻辑的**项 (term)**, **公式 (formula)**和**证明 (proof)**, 它们共同构成了一阶逻辑的语法部分. 项由变元和函数符号构成; 公式则由关系符号和逻辑符号构成. 粗略类比, 如果说符号相当于字, 那么项和公式则相当于词和句. 注意本篇所有内容都是以语言 `ℒ` 为参数的.

```agda
open import Foundation.Essential
open import FOL.Language.Base
module FOL.Syntax.Base (ℒ : Language) where
instance _ = ℒ
```

以下列出了本篇所引入的符号的优先级. 数字越大则优先级越高, 未列出的符号默认具有 20 的优先级. 它们的具体定义会在后文给出.

```agda
infix 4 _⊢_ _⊬_ _⊩_ _⊮_ ◌⊢_
infixr 15 _→̇_
infix 30 _[_]ₜ _[_]ₜ⃗ _[_]ᵩ _[_]₀
```

## 项

我们将使用 [De Brujin 索引](https://en.wikipedia.org/wiki/De_Bruijn_index) 实现量词的绑定, 因此项中使用自然数作为变元(名).

**<u>归纳定义</u>** 项

- 对任意自然数 `n`, `# n` 是项 (变元).
- 对任意 `l` 元函数符号 `f`, `f $̇ t⃗` 是项 (函数应用), 其中 `t⃗` 是项的 `l` 维向量.

```agda
data Term : 𝕋 where
  # : ℕ → Term
  _$̇_ : (f : 𝓕) → 𝕍 Term ∣ f ∣ᶠ → Term
```

由于项的定义内部涉及到项的向量, 它们相互影响, 直接对它们进行模式匹配是相对复杂的. 为此我们证明了一个辅助引理 `term-elim`, 用来对项进行结构归纳.

**<u>引理</u>** 项的结构归纳法: 任意给定项的性质 `P`, 可以证明任意项都满足 `P`, 只要证明以下两点

1. `P` 对所有变元成立
2. `P` 对所有形如 `f $̇ t⃗` 的项成立, 只要 `P` 对所有 `t ∈⃗ t⃗` 成立

**<u>证明</u>** 对项的结构归纳, 分两种情况

- 当项是变元时, 由前提1即证.
- 当项是函数应用 `f $̇ t⃗` 时, 由前提2, 只要证 `P` 对所有 `t ∈⃗ t⃗` 成立, 把它视作一个内部引理, 命名为 `H`. 我们递归证明 `H`, 给定 `t ∈⃗ t⃗`, 又分两种情况.
  - 当 `t` 位于 `t⃗` 的头部时, 用项的结构归纳法即证.
  - 当 `t` 位于 `t⃗` 的尾部时, 递归使用 `H` 即证. ∎

```agda
term-elim : {P : Term → 𝕋 ℓ} → (∀ n → P (# n)) →
  (∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → P t) → P (f $̇ t⃗)) → ∀ t → P t
term-elim H1 H2 (# n) = H1 n
term-elim {P} H1 H2 (f $̇ t⃗) = H2 f t⃗ H where
  H : ∀ {n} {t⃗ : 𝕍 Term n} t → t ∈⃗ t⃗ → P t
  H t (here refl) = term-elim H1 H2 t
  H t (there t∈⃗t⃗) = H t t∈⃗t⃗
```

### 项的替换

项的替换是指把一个项中所使用的所有变元分别替换成一些别的项. 这一操作是 De Brujin编码方案的一部分, 目的是为了实现量词绑定, 具体用法会在后面逐步说明. 首先为了实现项的替换, 我们需要一套替换规则, 它记录了全体自然数 (变元) 与项的一套对应关系.

**<u>定义</u>** 变元替换表 (`σ : Subst`) 是一个将变元映射到项的函数 `ℕ → Term`.

```agda
Subst : 𝕋
Subst = ℕ → Term
```

我们想要把变元替换表作用到项上, 这需要同时 (互递归) 定义单个项的替换 `t [ σ ]ₜ` 以及项的向量整体的替换 `t⃗ [ σ ]ₜ⃗`.

```agda
_[_]ₜ : Term → Subst → Term
_[_]ₜ⃗ : ∀ {n} → 𝕍 Term n → Subst → 𝕍 Term n
```

**<u>互递归定义</u>** 项的替换

- 单个项的替换 `t [ σ ]ₜ`:
  - 如果 `t` = `# n`, 则替换后为 `σ n`.
  - 如果 `t` = `f $̇ t⃗`, 则替换后为 `f $̇ t⃗ [ σ ]ₜ⃗`.
- 项的向量整体的替换 `t⃗ [ σ ]ₜ⃗`:
  - 如果 `t⃗` = `[]`, 则替换后为 `[]`.
  - 如果 `t⃗` = `t ∷ t⃗`, 则替换后为 `t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗`.

```agda
(# n)   [ σ ]ₜ = σ n
(f $̇ t⃗) [ σ ]ₜ = f $̇ t⃗ [ σ ]ₜ⃗

[] [ σ ]ₜ⃗ = []
(t ∷ t⃗) [ σ ]ₜ⃗ = t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗
```

标准库中定义了向量的高阶函数 `map⃗`, 用于对向量 `x⃗` 中的每个元素做相同变换 `f`, 所得到的向量记作 `map⃗ f x⃗`. 项的向量整体的替换 `t⃗ [ σ ]ₜ⃗` 也可以用 `map⃗` 来表示, 以套用库中关于 `map⃗` 的引理.

```agda
[]ₜ⃗≡map⃗ : ∀ {n} (t⃗ : 𝕍 Term n) σ → t⃗ [ σ ]ₜ⃗ ≡ map⃗ (_[ σ ]ₜ) t⃗
[]ₜ⃗≡map⃗ [] σ = refl
[]ₜ⃗≡map⃗ (_ ∷ t⃗) σ = cong (_ ∷_) $ []ₜ⃗≡map⃗ t⃗ σ
```

### 项的提升

**<u>定义</u>** 项 `t` 的提升 `↑ₜ t` 是指将 `t` 中涉及的所有变元 (自然数) 替换为其后继.

```agda
↑ₜ : Term → Term
↑ₜ = _[ # ∘ suc ]ₜ
```

例如, 若 `t` = `g $̇ (f $̇ # 0) ∷ [ # 1 ]`, 那么 `↑ₜ t` = `g $̇ (f $̇ # 1) ∷ [ # 2 ]`.

**<u>定义</u>** 替换表 `σ` 的提升 `↑ₛ σ` 是指对 `σ` 的值域中的项全部做一次提升, 得到替换表 `↑ₜ ∘ σ`, 然后使用希尔伯特旅馆操作把变元 `# 0` 插入到 `↑ₜ ∘ σ` 的头部, 得到 `# 0 ∷ₙ ↑ₜ ∘ σ`.

```agda
↑ₛ : Subst → Subst
↑ₛ σ = # 0 ∷ₙ ↑ₜ ∘ σ
```

之所以要做此种看似复杂的操作, 是因为后面我们会如此定义量词, 使得量词作用下的 `# 0` 被解释为量词的绑定变元, 它不应该受替换操作影响. 可以看到, `↑ₛ σ` 确实不会替换 `# 0`, 或者说替换后仍是 `# 0`. 而对于非绑定变元 (`# 1`, `# 2`, ...) 的替换, 需要保证替换后不会变成 `# 0`, 因此需要对 `σ` 的值域中的项全部做一次提升, 得到 `↑ₜ ∘ σ`, 以把 `# 0` 空出来. 总而言之, `↑ₛ σ` 对 `σ` 的定义域和值域都整体做了一次提升, 而空出来的 0 的位置仍然是 `# 0`.

## 公式

公式是定义逻辑符号的地方. 一般来说一阶逻辑的逻辑符号有

- 连词
  - 否定 $\neg$
  - 合取 $\land$
  - 析取 $\lor$
  - 蕴含 $\to$
  - 逻辑等价 $\leftrightarrow$
- 量词
  - 全称量化 $\forall$
  - 存在量化 $\exists$
- 等词 $=$

我们采用极简形式的公式定义, 只使用恒假 `⊥̇`, 蕴含 `→̇` 和全称量化 `∀̇` 这三个符号, 以方便证明一阶逻辑的元性质. 实际使用时, 否定, 合取, 析取, 逻辑等价和存在量化都可以用这三个符号来定义, 而等词则需要作为二元关系符号加入到语言中.

**<u>归纳定义</u>** 公式

- 恒假 `⊥̇` 是公式.
- 如果 `φ` 和 `ψ` 是公式, 那么 `φ →̇ ψ` 是公式.
- 如果 `φ` 是公式, 那么 `∀̇ φ` 是公式.
- 对任意 `l` 元关系符号 `R`, `R $̇ t⃗` 是公式, 其中 `t⃗` 是项的 `l` 维向量.

```agda
data Formula : 𝕋 where
  ⊥̇ : Formula
  _→̇_ : Formula → Formula → Formula
  ∀̇_ : Formula → Formula
  _$̇_ : (R : 𝓡) → 𝕍 Term ∣ R ∣ᴿ → Formula
```

### 公式的替换

**<u>递归定义</u>** 公式的替换 `φ [ σ ]ᵩ` 是指把变元替换表 `σ` 作用到公式 `φ` 中的所有项上.

- 如果 `φ` = `⊥̇`, 则没有项可被替换, 所以仍为 `⊥̇`.
- 如果 `φ` = `φ →̇ ψ`, 则分别替换 `_→̇_` 两边的公式, 再用 `_→̇_` 连接.
- 如果 `φ` = `∀̇ φ`, 则使用提升后的替换表 `↑ₛ σ` 替换 `φ` 后再做全称量化.
- 如果 `φ` = `R $̇ t⃗`, 则替换向量 `t⃗`, 再应用 `R`.

```agda
_[_]ᵩ : Formula → Subst → Formula
⊥̇       [ σ ]ᵩ = ⊥̇
(φ →̇ ψ) [ σ ]ᵩ = φ [ σ ]ᵩ →̇ ψ [ σ ]ᵩ
(∀̇ φ)   [ σ ]ᵩ = ∀̇ φ [ ↑ₛ σ ]ᵩ
(R $̇ t⃗) [ σ ]ᵩ = R $̇ map⃗ (_[ σ ]ₜ) t⃗
```

注意思考上面全称量化的情况是如何完成替换的, 结合 `↑ₛ σ` 的定义应该不难理解.

上面一系列提升和替换最终是为了实现以下概念.

**<u>定义</u>** 绑定变元的实例化 `φ [ t ]₀` 是指把公式 `φ` 中的 `# 0` 替换为项 `t`, 后继变元全部替换为其前驱.

```agda
_[_]₀ : Formula → Term → Formula
φ [ t ]₀ = φ [ t ∷ₙ # ]ᵩ
```

有了 `φ [ t ]₀` 的概念, 我们就可以说, 如果 `∀̇ φ` 成立, 那么对任意 `t`, `φ [ t ]₀` 也成立. 这就是全称量化的消去规则, 将加入到后文关于证明的定义中.

## 语境与理论

**<u>定义</u>** 公式的列表叫做语境 `Context`; 公式的集合叫做理论 `Theory`.

```agda
Context : 𝕋
Context = 𝕃 Formula

Theory : 𝕋₁
Theory = 𝒫 Formula
```

这两种概念的区别在于, 语境是保证有限的, 而理论则可能是无限集. 语境和理论中的元素又叫做**公理 (axiom)**.

**<u>定义</u>** 大蕴含: 设语境 `Γ` 等于 `φ₁ ∷ φ₂ ∷ ... ∷ [ φₙ ]`, 公式 `φ₁ →̇ φ₂ →̇ ... →̇ φₙ →̇ φ` 叫做 `Γ` 到 `φ` 的大蕴含式, 记作 `Γ ⇢ φ`.

```agda
_⇢_ : Context → Formula → Formula
[] ⇢ φ = φ
(ψ ∷ Γ) ⇢ φ = ψ →̇ Γ ⇢ φ
```

后文即将介绍的全称量化的引入规则中需要用到语境提升的概念, 而这又需要公式的提升, 它们都只是项的提升的简单推广.

**<u>定义</u>** 公式 `φ` 的提升 `↑ φ` 是指将 `φ` 中涉及的所有变元 (自然数) 替换为其后继.

```agda
↑_ : Formula → Formula
↑_ = _[ # ∘ suc ]ᵩ
```

**<u>定义</u>** 语境 `Γ` 的提升 `⭡ Γ` 是指提升 `Γ` 中所有的公式所得到的语境.

```agda
⭡ : Context → Context
⭡ = map ↑_
```

为了使后文更加简洁, 我们规定以下记号的类型:

```agda
variable
  t : Term
  φ ψ ξ : Formula
  Γ Δ : Context
  𝒯 : Theory
```

## 语法蕴含

有了以上准备, 我们终于可以定义什么叫证明, 也叫**语法蕴含 (syntactic consequence)**. 我们采用所谓[**自然演绎 (natural deduction)**](https://zh.m.wikipedia.org/zh/%E8%87%AA%E7%84%B6%E6%BC%94%E7%BB%8E)的方案.

**<u>归纳定义</u>** 语境 `Γ` 下对公式 `φ` 的证明树记作 `Γ ⊢ φ`, 它由且只由以下规则构造:

- 语境规则 `Ctx` : 如果 `φ` 是 `Γ` 中的公理, 那么有 `Γ ⊢ φ`.
- 蕴含的引入规则 `ImpI` : 如果 `φ` 加入到 `Γ` 后有 `ψ` 的证明树, 那么有 `Γ ⊢ φ →̇ ψ`.
- 蕴含的消去规则 `ImpE` : 如果有 `Γ ⊢ φ →̇ ψ` 且有 `Γ ⊢ φ`, 那么有 `Γ ⊢ ψ`.
- 全称量化的引入规则 `AllI` : 如果 `Γ` 在提升后有 `φ` 的证明树, 那么有 `Γ ⊢ ∀̇ φ`.
- 全称量化的消去规则 `AllE` : 如果有 `Γ ⊢ ∀̇ φ`, 那么对任意 `t` 有 ` Γ ⊢ φ [ t ]₀`.
- 恒假的消去规则 (爆炸律) `FalseE` : 如果有 `Γ` 下对恒假的证明树, 那么有 `Γ` 下对任意 `φ` 的证明树.
- 皮尔士公理 (排中律) `Peirce` : 无条件地, 有 `Γ ⊢ ((φ →̇ ψ) →̇ φ) →̇ φ`.

```agda
data _⊢_ : Context → Formula → 𝕋 where
  Ctx     : φ ∈͆ Γ            → Γ ⊢ φ
  ImpI    : φ ∷ Γ ⊢ ψ         → Γ ⊢ φ →̇ ψ
  ImpE    : Γ ⊢ φ →̇ ψ → Γ ⊢ φ → Γ ⊢ ψ
  AllI    : ⭡ Γ ⊢ φ           → Γ ⊢ ∀̇ φ
  AllE    : Γ ⊢ ∀̇ φ           → Γ ⊢ φ [ t ]₀
  FalseE  : Γ ⊢ ⊥̇             → Γ ⊢ φ
  Peirce  : ∀ φ ψ → Γ ⊢ ((φ →̇ ψ) →̇ φ) →̇ φ
```

**<u>注意</u>** 此处定义的 `Γ ⊢ φ` 是证明树, 它可能有多种构造方式, 也就是说它是**证明相关 (proof relevant)** 的. 它与传统上**证明无关 (proof irrelevant)** 的 $Γ ⊢ φ$ 略有不同. 对 `Γ ⊢ φ` 做命题截断就得到证明无关的版本 `∥ Γ ⊢ φ ∥₁`. 我们整体上采用延迟截断的方针, 不到必要时不截断.

**<u>定义</u>** 我们说 `Γ` 可证 `φ`, 记作 `Γ ⊢₁ φ`, 当且仅当存在 `Γ` 下对 `φ` 的证明树 `Γ ⊢ φ`.

```agda
_⊢₁_ : Context → Formula → 𝕋
Γ ⊢₁ φ = ∥ Γ ⊢ φ ∥₁
```

我们把“不能构造 `Γ ⊢ φ`” 记作 `Γ ⊬ φ`.

```agda
_⊬_ : Context → Formula → 𝕋
Γ ⊬ φ = ¬ (Γ ⊢ φ)
```

**<u>定义</u>** 理论 `𝒯` 下对公式 `φ` 的证明树, 记作 `𝒯 ⊩ φ` (“不能构造 `𝒯 ⊩ φ`” 记作 `𝒯 ⊮ φ`), 是一个二元组

1. 包含于 `𝒯` 的语境 `Γ`
2. `Γ` 下对 `φ` 的证明树 `Γ ⊢ φ`

其中语境 `Γ` 包含于理论 `𝒯` 是指 `Γ` 中的公理都属于 `𝒯`.

```agda
_⊩_ _⊮_ : Theory → Formula → 𝕋
𝒯 ⊩ φ = Σ Γ ， Γ ⊆̣͆ 𝒯 ∧ Γ ⊢ φ
𝒯 ⊮ φ = ¬ (𝒯 ⊩ φ)
```

**<u>定义</u>** 我们说 `𝒯` 可证 `φ`, 记作 `𝒯 ⊩₁ φ`, 当且仅当存在 `𝒯` 下对 `φ` 的证明树 `𝒯 ⊩ φ`.

```agda
_⊩₁_ : Theory → Formula → 𝕋
𝒯 ⊩₁ φ = ∥ 𝒯 ⊩ φ ∥₁
```

**<u>定义</u>** 我们说 `φ` 是恒真式 (或者说重言式, tautology), 当且仅当对任意 `Γ` 都有 `Γ ⊢ φ`, 记作 `◌⊢ φ`; 或者对任意 `𝒯` 都有 `𝒯 ⊩ φ`, 记作 `◌⊩ φ`

```agda
◌⊢_ : Formula → 𝕋
◌⊢ φ = ∀ {Γ} → Γ ⊢ φ

◌⊩_ : Formula → 𝕋₁
◌⊩ φ = ∀ {𝒯} → 𝒯 ⊩ φ
```

## 理论的一致性

**<u>定义</u>** 我们说理论 `𝒯` 一致, 当且仅当不存在从 `𝒯` 到恒假的证明.

```agda
Con : Theory → 𝕋
Con 𝒯 = 𝒯 ⊮ ⊥̇
```

**<u>定义</u>** 我们说 `𝒯₁` 相对于 `𝒯₂` 一致, 当且仅当存在 `𝒯₁` 到恒假的证明蕴含存在 `𝒯₂` 到恒假的证明.

```agda
Con_to_ : Theory → Theory → 𝕋
Con 𝒯₁ to 𝒯₂ = ∥ 𝒯₁ ⊩ ⊥̇ ∥₁ → ∥ 𝒯₂ ⊩ ⊥̇ ∥₁
```

**<u>事实</u>** 相对一致性: 如果 `𝒯₁` 相对于 `𝒯₂` 一致, 那么 `𝒯₂` 的一致性蕴含 `𝒯₁` 的一致性.  
**<u>证明</u>** 依定义. ∎

```agda
relative-consistency : ∀ {𝒯₁ 𝒯₂} → Con 𝒯₁ to 𝒯₂ → Con 𝒯₂ → Con 𝒯₁
relative-consistency H₁₂ ¬H₂ H₁ = 𝟙.rec isProp⊥ ¬H₂ (H₁₂ ∣ H₁ ∣₁)
```

**<u>事实</u>** 相对一致的传递性: 如果 `𝒯₁` 与 `𝒯₂` 相对一致, 且 `𝒯₂` 与 `𝒯₃` 相对一致, 那么 `𝒯₁` 与 `𝒯₃` 相对一致.  
**<u>证明</u>** 依定义. ∎

```agda
Con-trans : ∀ {𝒯₁ 𝒯₂ 𝒯₃} → Con 𝒯₁ to 𝒯₂ → Con 𝒯₂ to 𝒯₃ → Con 𝒯₁ to 𝒯₃
Con-trans con₁ con₂ = con₂ ∘ con₁
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Base.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Base.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.base)  
> 交流Q群: 893531731
