#import "template.typ": *
#import "@preview/rubby:0.10.1": get-ruby

#show: project.with(
  title: "Smullyanのシステムの形式化について",
  authors: ("SnO2WMaN",),
)

#let Pred = $serif("Pred")$
#let Sent = $serif("Sent")$
#let Pow(s) = $cal("P")(#s)$
#let True = $serif("True")$
#let False = $serif("False")$
#let setminus = $backslash$

#let Tr = $serif("Tr")$

#let And = $class("relation", amp)$

#heading(numbering: none)[メタ情報] <sect:meta>

この文書は#link("https://adventar.org/calendars/10209")[証明支援系 Advent Calendar 2024]の3日目の記事です．

この文書について
- #link("https://sno2wman.github.io/notes-on-smullyanTP/main.pdf") で最新のPDFをダウンロードできます．
- #link("https://github.com/SnO2WMaN/notes-on-smullyanTP") で誤植訂正やコメントなどを受け付けています．
- #link("https://github.com/SnO2WMaN/notes-on-smullyanTP/blob/main/LICENSE")[CC-BY-4.0]でライセンスされています．

この文書に載せられたコードの全文は#link("https://github.com/SnO2WMaN/smullyanTP")で公開しています．

= はじめに <sect:intro>

論理学では自己言及的，パラドキシカルな事実が成り立つことが知られている．
この文書はそれらの事実を解説する目的ではないので，詳細に関しては書かずに大雑把に述べることにする．
太字の強調部分だけ読めば，とりあえず本文の理解には問題ないだろう．

以下 $T$ は適当な算術の理論とする．

#theorem([Gödel-Rosserの第一不完全性定理])[
  無矛盾な理論 $T$ について，$T$ 上で*証明も反証も出来ない命題が存在する．*
  すなわち，次のような文 $G_T$ が存在する：$T &nvdash G_T$ かつ $T &nvdash not G_T$．
]<thm:goedel_rosser_first_incompleteness>

普通は第一不完全性定理ではそのような命題が実際に真であるのかについては言及しない．
ただし，真偽について言及するとキャッチーなので，次の形で述べられることもある#footnote[このような解説の是非については#cite(<kikuchi_2014>)に少し説明がある．]．

#theorem([Boolos?])[
  無矛盾な理論 $T$ について，*正しいが証明できない命題が存在する．*
  すなわち，次のような文 $G_T$ が存在する：$NN &vDash G_T$ かつ $T &nvdash G_T$．
]<thm:boolos_incompleteness>

不完全性定理の証明，あるいはより一般に自己言及的な事実を示すためには，次の不動点補題（対角化補題などいろいろな呼び方がある）が鍵となる．

#theorem([不動点補題])[
  $phi(x)$ は $x$ のみを自由変数とする論理式とする．次の文 $F_phi$ が存在する．
  $
    T vdash F_phi <-> phi (ulcorner F_phi urcorner)
  $
  この意味で，$F_phi$ を $phi$ の不動点という．
]<thm:carnap_fixpoint>

また，次の命題も重要である．

#theorem([Tarskiの定義不可能性定理])[
  *真であるという性質は記述できない．*すなわち，次のような論理式 $True(x)$ は存在しない：任意の論理式 $phi$ について，
  $
    NN vDash phi <-> True(ulcorner phi urcorner)
  $
]<thm:tarski_undefinability>

論理パズルの一般書などでも有名な論理学者Smullyanは#cite(<smullyan_truth_2013>)で，これらの定理を一般の読者に向けて説明するために，
文字列の操作だけによる非常に簡単な形式体系を導入して，
よく似た現象が起こることを示した．
この文書では#cite(<smullyan_truth_2013>)を精査，整理し直した#cite(<kurahashi_smullyans_2024>)を参考に，Smullyanの形式体系を実際にLeanで形式化して定理を証明した．
コードは300行程度で済んでいるので，興味のある読者は実際にコードを読んだり触ってみることを勧める．


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

また，$M$ の述語 $H$ に対して $Phi_M (H)$ を `H.valuated` で表すことにする．

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

  -- `S : M.Sentence` を `M.Word` として扱いたい場合は `pred` と `word` を単純に連結したものとする．
  def Sentence.toWord : M.Sentence → M.Word := fun ⟨H, X⟩ => ↑H ++ X

  -- `↑S` と書けば `M.Word` として扱えるようになる．
  instance : Coe (M.Sentence) (M.Word) := ⟨Sentence.toWord⟩
  ```
]

#remark[
  ここでは元の論文とは違う方針で文を定義している（本質的には同じ）．
  元の定義は「$M$ の語 $S$ が $M$ の文であるとは，$S equiv H X$ となる $H in Pred_M$ と $X in Sigma^*_M$ が存在することをいう」となっている．

  これを素直に定義すると以下のようになる．ここで，`↑H` は `Predicate` 型の要素を `Word` 型の要素にキャストしている#footnote[Coercionと呼ぶ．今，`X`は型`M.Word`の要素だが，`H`は型`M.Predicate`の要素である．`++`すなわち関数`List.append`の型は`List α → List α → List α`であるため，`H ++ X`とすると型が合わない．そのためCoercionが必要となる．]と思ってもらえれば良い．

  #code[
    ```lean
    def isSentence {M : SmullyanModel} (S : M.Word) : Prop := ∃ (H : M.Predicate) (X : M.Word), S = ↑H ++ X
    ```
  ]

  しかしこの定義は使いづらい．なぜならば `S`に対して*具体的に*`H`と`X`が何なのかの情報を持っておらず，ただ存在することだけを主張しているからである．
  `S.isSentence`という命題からそのような性質を満たす`H`を取り出すには`Exists.choice`を使う必要がある．
  この操作はLeanにおいては超越的な/非構成的な操作であり，また単純にこれを毎回書くのは面倒というデメリットがある．
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
  文の集合 $True_M$ を次のように定義する．
  $
    True_M &:= { angle.l H, X angle.r in Sent_M | X in Phi_M (H)} \
  $
  文 $S$ が $S in True_M$ のとき，$S$ が（$M$ で）真であるといい $vDash S$ と書く．
  逆に $S in.not True_M$ のとき，$S$ が（$M$ で）真でないという．
]

これをコードに書き下すと次のようになる．

#code[
  ```lean
  def true_sentences (M : SmullyanModel) : Set M.Sentence := fun ⟨H, X⟩ => X ∈ H.valuated

  def Sentence.isTrue (S : M.Sentence) := S ∈ M.true_sentences

  prefix:50 "⊨ " => Sentence.isTrue
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

これをコードに書き下すと次のようになる．`nH`のようにそのまま記号として使うとよくわからなくなるので`~H`で表すことにする．

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
  $vDash mono(n) S$ を $nvDash S$ と書き，$S$ の否定が真であることを表す．
]

$S$ の否定が真であることと，$S$ が真でないことは一致してほしいが，実際そうなる．

#lemma[
  $nvDash S <==> S in.not True_M$．
] <lem:neg_true_iff_not_true>

#proof[
  $S = angle.l H, X angle.r$ とする．定義に沿って変形していく．
  $
    nvDash angle.l H, X angle.r
    &<==> vDash mono(n) angle.l H, X angle.r \
    &<==> vDash angle.l mono(n) H, X angle.r \
    &<==> X in Phi_M (mono(n) H) \
    &<==> X in Sigma^*_M setminus Phi_M (H) \
    &<==> X in.not Phi_M (H) \
    &<==> angle.l H, X angle.r in.not True_M
  $
  以上より $nvDash S <==> S in.not True_M$ である．
]

元の文の否定の否定が真なら，元の文も真である．すなわち二重否定は元に戻ることも確認出来る．

#lemma[
  $nvDash mono(n) S <==> vDash S$．
] <lem:neg_not_true_iff_true>

#proof[
  定義に沿って変形すればよい．
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

冒頭で，自己言及的な事実を示すためには#ref(<thm:carnap_fixpoint>)が重要であると述べた．
このシステム上では#ref(<thm:smullyan_fixpoint>)がその定理に対応する．

#definition[不動点][
  $M$ は $mono(r)$-モデルとする．
  $H$ を $M$ の述語として，文 $F = angle.l mono(r) H, mono(r) H angle.r$ を $H$ の不動点という．
]

#theorem[不動点定理][
  任意の述語 $H$ に対し，$H$ の不動点 $F$ は次の性質が成り立つ．
  $
    vDash F <==> vDash H F
  $
]<thm:smullyan_fixpoint>

#proof[
  定義に沿って次の同値が成り立つ．
  $vDash mono(r) H mono(r) H
    <==> mono(r) H in Phi_M (mono(r) H)
    <==> mono(r) H mono(r) H in Phi_M (H)
    <==> vDash H mono(r) H mono(r) H$．
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
  まず，不動点の定義より次の同値が成り立つ．
  $
    vDash F <==> vDash mono(n) H F <==> nvDash H F
  $ <eq:lem:fixpoint_prop_1>
  #ref(<lem:neg_true_iff_not_true>)から $nvDash H F <==> H F in.not True_M <==> F in.not Phi_M (H)$ が成り立つのでよい．
]


== 主定理

それではこのシステム上で成り立つ，2つの主定理を示す．

まずは#ref(<thm:theorem_T>)から．これは#ref(<thm:tarski_undefinability>)に対応する定理である．

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

次に#ref(<thm:theorem_G>)を示す．これは#ref(<thm:goedel_rosser_first_incompleteness>)と#ref(<thm:boolos_incompleteness>)に対応する定理である．

#theorem[Theorem G][
  $M$ は $mono("nr")$-モデルとし，述語 $H$ は $Phi_M (H) subset.eq True_M$ を満たすものとする．
  このとき，$F in.not Phi_M (H)$ かつ $mono(n) F in.not Phi_M (H)$ となる文 $F$ が存在する．
]<thm:theorem_G>

#proof[
  $mono(n) H$ の不動点を $F$ とするとこれが所望の文となる．

  今，$vDash F$ としてよい．なぜなら仮に $vDash F$ でないと仮定すると，#ref(<lem:fixpoint_prop>) より $F in Phi_M (H)$ が言えて，$Phi_M (H) subset.eq True_M$ であるため $vDash F$ となっておかしい．

  まず#ref(<lem:fixpoint_prop>)より直ちに $F in.not Phi_M (H)$ が従う．

  次に $mono(n) F in.not Phi_M (H)$ だが，これは $Phi_M (H) subset.eq True_M$ だから $mono(n) F in.not True_M$ を示せば十分．
  そして#ref(<lem:neg_true_iff_not_true>)と#ref(<lem:neg_not_true_iff_true>)から次の同値関係
  $mono(n) F in.not True_M <==> nvDash mono(n) F <==> vDash F$
  が成り立つのでよい．
]

#remark[
  ここではわかりやすく「存在する」と書いたが，もちろん今までの方針と同じ様に#ref(<lem:fixpoint_prop>)の不動点がその性質を満たす具体例であるとして形式化してもよい．
]

= おわりに

いくつかの証明は定義より明らかなので，単純に簡約化(`simp`)すれば自明に済ませることが出来る．
今回の形式化では300行程度のコードで済んでいるが，より精緻な分析や，算術上で実際にSmullyanモデルを上手く作れることなどの形式化について，上手くいくかは不明．
