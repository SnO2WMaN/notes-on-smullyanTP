#import "template.typ": *

#show: project.with(
  title: "Smullyanのシステムの形式化について",
  authors: ("SnO2WMaN"),
)

#let Pred = $serif("Pred")$
#let Sent = $serif("Sent")$
#let Pow(s) = $cal("P")(#s)$
#let True = $serif("True")$
#let False = $serif("False")$
#let setminus = $backslash$

#let And = $class("relation", amp)$

= はじめに <sect:intro>

@kurahashi_smullyans_2024 に沿って，Smullyanのシステムを形式化する．

= 本文

== 文字列

#definition([文字列])[
  - 非空集合 $Sigma$ をアルファベットとする．
  - $Sigma^*$ は $Sigma$ 上の文字列の集合とする．
  - 空の文字列を $epsilon.alt$ で表す．
  - 文字列 $X,Y in Sigma^*$ に対し，$X Y$ は $X$ と $Y$ の連結を表す．
  - $X$ と $Y$ が記号列として等しいとき，$X equiv Y$ と書く．
]

今回の形式化では，文字列は`List α`で表現する．ここでは`α`はアルファベットを表す型である．

== Smullyanモデル <sect:smullyan>

#definition([Smullyanモデル])[
  以下を満たす3つ組 $angle.l Sigma, Pred, Phi angle.r$ をSmullyanモデルという．
  1. $Sigma$ はアルファベット．
  2. $Pred$ は $Sigma^*$ の部分集合であり次を満たす．
    - $H in Pred, X in Sigma^* backslash {epsilon.alt}$ に対し，$H X in.not Pred$ を満たす．
  3. $Phi$ は 写像 $Pred -> Pow(Sigma^*)$．

  Smullyanモデル $M = angle.l Sigma, Pred, Phi angle.r$ の構成要素 $Sigma, Pred, Phi$ をそれぞれ $Sigma_M, Pred_M, Phi_M$ と書く．
  更に $Sigma_M^*$ の元を $M$ の語，$Pred_M$ の元を $M$ の述語と呼ぶ．

]

#code[
  ```lean
  structure SmullyanModel where
    α : Type*
    isPredicate : List α → Prop
    isPredicate_spec :
      ∀ H : { H // isPredicate H }, ∀ x ≠ [], ¬isPredicate (H.val ++ x)
    valuation : { H // isPredicate H } → Set (List α)
  ```
]

Leanでは`α`の素朴な集合の型`Set α`は，`α`から`Prop`への関数の型`α → Prop`の略記として定義されることに注意する．
`{ x // isPredicate x }` と書くことで，`List α` で `isPredicate` を満たすような部分型(`Subtype`)，すなわち $Pred$ の型を表す．

これらを毎回書くのは面倒なので，略記を導入する．$Sigma^*_M, Pred_M$ に対応している．

#code[
  ```lean
  abbrev Word (M : SmullyanModel) := List M.α

  abbrev Predicate (M : SmullyanModel) := { H // M.isPredicate H }
  ```
]

また，$M$ の述語 $H in Pred_M$ に対して $Phi_M (H)$ によって定まる語の集合を `H.valuated` で表すことにする．

#code[
  ```lean
  def Predicate.valuated {M : SmullyanModel} (H : Predicate M) : Set (Word M) := M.valuation H
  ```
]

#definition[規定する][
  $H$ を $M$ の述語，$V$ を $M$ の語の集合 とする．$Phi_M (H) = V$ であるとき，$H$ は $V$ を規定するという．
]

これは素直に形式化出来る．

#code[
  ```lean
  def Predicate.names {M : SmullyanModel} (H : M.Predicate) (V : Set M.Word) : Prop := H.valuated = V
  ```
]

次に，$M$ の文を定義する．

#definition([文])[
  $M$ の述語 $H$ と語 $X$ の組 $angle.l H,X angle.r$ を $M$ の文という．
  $M$ 文の集合を $Sent_M$ と書く．
  適宜，文 $M = angle.l H,X angle.r$ は $H X$ として語のように扱ってよいことにする．
]

#code[
  ```lean
  structure Sentence (M : SmullyanModel) where
    pred : M.Predicate
    word : M.Word

  def Sentence.toWord : M.Sentence → M.Word := fun ⟨H, X⟩ => ↑H ++ X

  instance : Coe (M.Sentence) (M.Word) := ⟨Sentence.toWord⟩
  ```
]

#remark[
  ここでは元の論文とは違う方針で文を定義している（本質的には同じ）．
  元の定義はこうなっている．

  #definition([文], numbering: none)[
    $M$ の語 $S$ が $M$ の文であるとは，$S equiv H X$ となる $H in Pred_M$ と $X in Sigma^*_M$ が存在することをいう．
  ]

  これを素直に定義すると以下のようになる．ここで，`↑H` は `Predicate` 型の要素を `Word` 型の要素にキャストしている#footnote[Coercionと呼ぶ．今，`X`は型`M.Word`の要素だが，`H`は型`M.Predicate`の要素である．`++`すなわち関数`List.append`の型は`List α → List α → List α`であるため，`H ++ X`とすると型が合わない．そのためCoercionが必要となる．]と思ってもらえれば良い．

  #code[
    ```lean
    def isSentence {M : SmullyanModel} (S : M.Word) : Prop := ∃ (H : M.Predicate) (X : M.Word), S = ↑H ++ X
    ```
  ]

  しかしこの定義は使いづらい．なぜならば `S`に対して*具体的に*`H`と`X`が何なのかの情報を持っておらず，ただ存在することだけを主張しているからである．
  `S.isSentence`という命題からそのような性質を満たす`H`を取り出すには`Classical.choice`を使う必要がある．
  この操作はLeanにおいては超越的な操作であり，また単純にこれを毎回書くのは面倒というデメリットがある．
  したがって，より簡単に扱うために，文を構成する述語と語の組を直接扱うことにした．
] <rmk:sentence>

重要な補題である文の一意性を示す．

#lemma[文の一意性][
  $S in Sent_M$ に対して $S equiv H X$ となる述語 $H$ は一意である．
]<lem:uniqueness_of_sent_pred>

#proof[
  一意でないと仮定して矛盾を導く．
  $S equiv H X$ と $S equiv H' X'$ であり，$H equiv.not H'$ となる述語 $H, H'$ が存在すると仮定する．

  今，一般性を失わずに $H$ は $H'$ を始める真の部分列，すなわち $H' equiv H Y$ となる $Y equiv.not epsilon$ が存在するとしてよい．
  すると $H$ は述語であるので $H Y in.not Pred_M$ であり，よって $H' in.not Pred_M$ となる．これはおかしい．
]

#example[
  例えば $angle.l mono("ab"), mono("cde") angle.r$ は $M$ の文であるとすると，この文は語 $mono("abcde")$ として表される．
  @lem:uniqueness_of_sent_pred は，$mono("abcde")$ となるような文の候補として $angle.l mono("abc"), mono("bc") angle.r$ や $angle.l mono("a"), mono("bcde") angle.r$ があるが，これらは $M$ の文にはなり得ないということを保証する．
]

更に形式化上では，後の証明で使う次の補題を示しておく．

#code[
  ```lean
  /--
    `Sentence.toWord` は単射である，
    すなわち：
      - `S₁.toWord = S₂.toWord → S₁ = S₂`
      - `S₁` と `S₂` が文字列として等しいならば，`S₁` と `S₂` の構成要素 `pred, word` は互いに等しい．
  -/
  lemma toWord_injective
    : Function.Injective (Sentence.toWord (M := M)) := by ...
  ```
]


次に，モデル上の文の真偽を定める．

#definition[文の真偽][
  文の集合 $True_M$ と $False_M$ を次のように定義する．
  $
    True_M &:= { angle.l H, X angle.r in Sent_M | X in Phi_M (H)} \
    False_M &:= Sent_M setminus True_M
  $
  文 $S$ が $S in True_M$ のとき，$S$ が（$M$ で）真であるといい，これを $vDash S$ と書く．
  逆に，$S in False_M$ のとき，$S$ が （$M$ で）偽であるという．
]

#code[
  ```lean
  def true_sentences (M : SmullyanModel) : Set M.Sentence := fun ⟨H, X⟩ => X ∈ H.valuated

  def Sentence.isTrue (S : M.Sentence) := S ∈ M.true_sentences

  prefix:50 "⊨ " => Sentence.isTrue

  def false_sentences (M : SmullyanModel) : Set M.Sentence := M.true_sentencesᶜ
  ```
]

次に，Smullyanモデル上で特別な働きを行う $mono(n)$ および $mono(r)$ という記号を導入する．

$mono(n)$ は否定(negation)を意図した記号である．
#definition([$mono(n)$-Smullyanモデル])[
  $M$ が $mono(n)$-Smullyanモデルであるとは，次の条件を満たすアルファベット $mono(n) in Sigma_M$ が存在することをいう．
  1. $H in Pred_M$ に対し $mono(n) H in Pred_M$．
  2. $Phi_M (mono(n) H) = Sigma^*_M setminus Phi_M (H)$．

  文 $S = angle.l H,X angle.r$ に対して，その否定の文 $mono(n) S = angle.l mono(n) H, X angle.r$ とする．
]


#code[
  ```lean
  class SmullyanModel.IsN (M : SmullyanModel) where
    n : M.α
    n_spec₁ : ∀ H : M.Predicate, (M.isPredicate (n :: H))
    n_spec₂ : ∀ H : M.Predicate, M.valuation ⟨n :: H, n_spec₁ H⟩ = (H.valuated)ᶜ

  variable [M.IsN] -- 以下 `M` は `IsN` であると仮定する

  -- `n ++ H`（定義）と，実際にそれは `M.Predicate` である（証拠）の組で述語の否定を定義．
  def Predicate.neg (H : M.Predicate) : M.Predicate := ⟨IsN.n :: H.val, IsN.n_spec₁ H⟩

  -- `~H` で述語の否定を表すこととする．
  prefix:90 "~" => Predicate.neg

  -- 元の `pred` の部分を否定して文の否定とする．
  def Sentence.neg (S : M.Sentence) : M.Sentence := ⟨~S.pred, S.word⟩

  -- `~S` で文の否定を表すこととする．
  prefix:90 "~" => Sentence.neg
  ```
]

#definition[
  $vDash mono(n) S$ を $nvDash S$ と書いて，$S$ は真ではないという．
]

真でないことと偽であるというのは当然一致してほしいが，実際そうなる．

#lemma[
  $nvDash S <==> S in False_M$．
]

#proof[
  $S = angle.l H, X angle.r$ とする．定義に沿って変形していく．
  $
    nvDash angle.l H, X angle.r
    &<==> vDash mono(n) angle.l H, X angle.r \
    &<==> vDash angle.l mono(n) H, X angle.r \
    &<==> X in Phi_M (mono(n) H) \
    &<==> X in Sigma^*_M setminus Phi_M (H) \
    &<==> X in.not Phi_M (H) \
    &<==> angle.l H, X angle.r in.not True_M \
    &<==> angle.l H, X angle.r in False_M
  $
  以上より $nvDash S <==> S in False_M$ である．
]

/*
#lemma[
$M nvDash mono(n) S <==> M vDash S$．
すなわち文を二重否定すると元に戻る．$M vDash mono(n) mono(n) S <==> M vDash S$．
]
*/

$mono(r)$ は繰り返し(repeated)を意図した記号であり，この記号によって不動点の構成が可能になる．

#definition([$mono(r)$-Smullyanモデル])[
  $M$ が $mono(r)$-Smullyanモデルであるとは，次の条件を満たすアルファベット $mono(r) in Sigma_M$ が存在することをいう．
  1. $H in Pred_M$ に対し $mono(r) H in Pred$
  2. $Phi_M (mono(r) H) = {K in Pred_M | K K in Phi_M (H)}$
]

== 不動点定理

#definition[不動点][
  $M$ は $mono(r)$-モデルとする．
  $H$ を $M$ の述語として，文 $F = angle.l mono(r) H, mono(r) H angle.r$ を $H$ の不動点という．
]

#theorem[不動点定理][
  任意の述語 $H$ に対し，$H$ の不動点 $F$ は次の性質が成り立つ．
  $
    vDash F <==> vDash H F
  $
]

#remark[
  元の論文では不動点定理は「$vDash F <==> vDash H F$ となる $F$ が任意の $H$ に対して存在する」という形で言及されている．
  しかし @rmk:sentence でも述べたように，存在するという形の言明は実際に構成できるならば構成したほうが扱いやすくてよいという方針で形式化を進めている．
]

最後に，主定理の証明において頻繁に用いる，述語の否定の不動点に関しての補題を示す．

#lemma[
  $M$ は $mono("nr")$-モデル とする．
  任意の述語 $H$ に対し，$mono(n) H$ の不動点を $F$ とする．
  このとき $vDash F <==> F in.not Phi_M (H)$
]<lem:fixpoint_prop>

#proof[
  $vDash F <==> vDash mono(n) H F <==> nvDash H F <==> F in.not Phi_M (H)$．
]


== 主定理

それでは2つの主定理を示す．まずは#ref(<thm:theorem_T>)から．

#theorem[Theorem T][
  $M$ は $mono("nr")$-モデル であるとする．
  $True_M$ を規定する述語は存在しない．
]<thm:theorem_T>

#proof[
  仮に $H$ としてそのような述語が存在するとして矛盾を導く．

  $F$ を $mono(n) H$ の不動点とする．
  仮定より $Phi_M (H) = True_M$ だから，$F in Phi_M (H) <==> vDash F$ が成立する．
  #ref(<lem:fixpoint_prop>) と $F$ の定義より $vDash F <==> F in.not Phi_M (H)$ が成り立つ．
  これらを合わせると $F in Phi_M (H) <==>  F in.not Phi_M (H)$ となっておかしい．
]

次に#ref(<thm:theorem_G>)を示す．

#theorem[Theorem G][
  $M$ は $mono("nr")$-モデルとし，述語 $H$ は $Phi_M (H) subset.eq True_M$ を満たすものとする．
  このとき，$F in.not Phi_M (H)$ かつ $mono(n) F in.not Phi_M (H)$ となる文 $F$ が存在する．
]<thm:theorem_G>

#proof[
  $mono(n) H$ の不動点を $F$ とするとこれが所望の文となる．

  今，$vDash F$ としてよい．なぜなら仮に $vDash F$ でないと仮定すると，#ref(<lem:fixpoint_prop>) より $F in Phi_M (H) subset.eq True_M$ が言えるので $vDash F$ でありおかしい．

  まず，#ref(<lem:fixpoint_prop>)より $F in.not Phi_M (H)$ が従う．

  次に，$vDash F ==> vDash mono(n) H F ==> nvDash H F ==> H F in False_M ==> mono(n) F in.not Phi_M (H)$ が成立する．
]

#remark[
  ここではわかりやすく「存在する」と書いたが，もちろん今までの方針と同じ様に#ref(<lem:fixpoint_prop>)の不動点がその性質を満たす具体例であるとして形式化してもよい．
]
