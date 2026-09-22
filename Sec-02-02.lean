inductive myType : Type where
  | Nat
  | Bool

open myType

-- indexed family type（Leadだと indexed inductive family のほうが一般的？）
-- TPlusで言えば「Nat Nat Nat」がindex
-- これにより、tbinop a b c というfamilyの値（tbinop の一つの型）を一つ決めている
-- 事実上のGADT
-- TPlusやTTimesと、TEqとを、tbinopの型として書けるのは、GADTであるのおかげ（普通の ADT なら、同じデータ型のコンストラクタは基本的に同じ形の結果型を返す）

inductive tbinop : myType → myType → myType → Type where
  | TPlus : tbinop Nat Nat Nat
  | TTimes : tbinop Nat Nat Nat
  | TEq : ∀ t, tbinop t t Bool -- CPDTはこれ
--  | TEq : {t : myType} → tbinop t t Bool -- Leanならtが暗黙引数でいいんじゃないか → t自体にパターンマッチさせたいのでダメ
  | TLe : tbinop Nat Nat Bool

inductive texp : myType → Type where
  | TNConst : Nat → texp Nat
  | TBConst : Bool → texp Bool
  | TBinop : ∀ {t1 t2 t3}, tbinop t1 t2 t3 → texp t1 → texp t2 → texp t3

-- 対象言語の型や式を、Leanの型に対応させる関数たち

open tbinop texp

def type_denote (t : myType) : Type :=
  match t with
  | myType.Nat => Nat
  | myType.Bool => Bool

def tbinop_denote arg1 arg2 arg3 (b : tbinop arg1 arg2 arg3) :
        type_denote arg1 → type_denote arg2 → type_denote arg3 :=
  match (generalizing := true) b with
  | TPlus => Nat.add
  | TTimes => Nat.mul
  | TEq myType.Nat => Nat.beq
  | TEq myType.Bool => fun (b1 b2 : Bool) => b1 == b2 -- BEq.beqがCoqのeqbに相当するようなのだが、暗黙引数の型をBEq.beq (α := Bool)のように指定しないとsynthesizeが通らない
  | TLe => Nat.ble

def texp_denote t (e : texp t) : type_denote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop b e1 e2 =>
    (tbinop_denote _ _ _ b) (texp_denote _ e1) (texp_denote _ e2)

#eval texp_denote Nat (TNConst 42) -- 42
#eval texp_denote Bool (TBConst true) -- true
#eval texp_denote Nat (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) -- 28
#eval texp_denote Bool (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) -- false
#eval texp_denote Bool (TBinop TLe (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) -- true

-- スタックマシンの実装（CPDT 2.2.2）

def tstack := List myType

inductive tinstr : tstack → tstack → Type where
  | TiNConst : ∀s, Nat → tinstr s (Nat :: s)
  | TiBConst : ∀s, Bool → tinstr s (Bool :: s)
  | TiBinop : ∀{arg1 arg2 res s},
      tbinop arg1 arg2 res → tinstr (arg1 :: arg2 :: s) (res :: s)

inductive tprog : tstack → tstack → Type where
  | TNil : ∀s, tprog s s
  | TCons : ∀{s1 s2 s3}, tinstr s1 s2 → tprog s2 s3 → tprog s1 s3

def vstack (ts : tstack) : Type :=
  match ts with
  | [] => Unit
  | t :: ts' => type_denote t × vstack ts'

open tinstr tprog

-- vstack tsの型は定義によりtsに依存している。
-- もしtinstr_denote自体を、「vstack tsを引数としてvstack ts'を返す関数」として定義してしまうと、
-- 「引数iに応じてtsを別の具体的な形として扱う」ことができなくなる。
-- （iとして渡されるtsにより、matchに入る前にvstack tsの型が固定されてしまうから。）
-- tinstr_denoteを「vstack ts'型の値を返す無名関数」を返すように定義すれば、
-- vstack tsの型が固定されるのをぎりぎりまで遅らせることができる。

def tinstr_denote {ts ts'} (i : tinstr ts ts') : vstack ts → vstack ts' :=
  match i with
  | TiNConst _ n => fun s => (n, s)
  | TiBConst _ b => fun s => (b, s)
  | TiBinop b => fun s =>
     let (arg1, (arg2, s')) := s
     ((tbinop_denote _ _ _ b) arg1 arg2, s')

def tprog_denote {ts ts'} (p : tprog ts ts') : vstack ts → vstack ts' :=
  match p with
  | TNil _ => fun s => s
  | TCons i p' => fun s =>
    let s' := tinstr_denote i s
    tprog_denote p' s'

-- 2.2.3 プログラムの逐次実行

def tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
  | TNil _ => fun p' => p'
  | TCons i p1 => fun p' => TCons i (tconcat _ _ _ p1 p')

def tcompile {t} (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
  | TNConst n => TCons (TiNConst _ n) (TNil _)
  | TBConst b => TCons (TiBConst _ b) (TNil _)
  | TBinop b e1 e2 => tconcat _ _ _ (tcompile e2 _)
      (tconcat _ _ _ (tcompile e1 _) (TCons (TiBinop b) (TNil _)))

#print tcompile
#eval tprog_denote (tcompile (TNConst 42) []) () -- (42, ())

-- 2.2.4 証明

theorem tconcat_correct : ∀{ts ts' ts''} (p : tprog ts ts')
  (p' : tprog ts' ts'') (s : vstack ts),
  tprog_denote (tconcat _ _ _ p p') s = tprog_denote p' (tprog_denote p s) := by
  intro ts ts' ts'' p p' s
  induction p
  case TNil _ =>
    rfl
  case TCons _ _ _ i p1 ih =>
    simp [tconcat, tprog_denote]
    rw [ih]

theorem tcompile_correct_aux : ∀{t} (e : texp t) ts (s : vstack ts),
  tprog_denote (tcompile e ts) s = (texp_denote _ e, s) := by
  intro t e
  induction e
  case TNConst n =>
    intro ts s
    rfl
  case TBConst b =>
    intro ts s
    rfl
  case TBinop b e1 e2 ih1 ih2 =>
    intro ts s
    simp [tcompile]
    rw [tconcat_correct]
    rw [ih2]
    rw [tconcat_correct]
    rw [ih1]
    rfl

theorem tcompile_correct : ∀{t} (e : texp t),
  tprog_denote (tcompile e []) () = (texp_denote _ e, ()) := by
  intro t e
  exact tcompile_correct_aux e [] ()
