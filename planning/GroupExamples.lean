import AlgebraBook.GroupBasics

/-!
군의 예와 거듭제곱을 집필하기 전에 작성한 정의와 핵심 증명의 구현 확인.
독자용 본문은 2장의 정의, 기본 계산, 구체적인 예와 자동화 절에 수록한다.
-/

namespace Course.Preparation

variable {A B : Type}

theorem inv_inv (G : Group A) (a : A) :
    G.inv (G.inv a) = a := by
  have h : a = G.inv (G.inv a) := by
    apply inverse_unique G (G.inv a) a
    exact G.inv_right a
  exact h.symm

theorem inv_id (G : Group A) : G.inv G.id = G.id := by
  symm
  apply inverse_unique G G.id G.id
  exact G.id_left G.id

theorem inv_op (G : Group A) (a b : A) :
    G.inv (G.op a b) = G.op (G.inv b) (G.inv a) := by
  symm
  apply inverse_unique G (G.op a b)
  -- 곱의 왼쪽에 역원을 놓고 이웃한 원소와 역원을 차례로 소거한다.
  calc
    G.op (G.op (G.inv b) (G.inv a)) (G.op a b) =
        G.op (G.inv b) (G.op (G.inv a) (G.op a b)) := by
      rw [G.assoc]
    _ = G.op (G.inv b) (G.op (G.op (G.inv a) a) b) := by
      rw [G.assoc]
    _ = G.op (G.inv b) b := by rw [G.inv_left, G.id_left]
    _ = G.id := by exact G.inv_left b

def power (G : Group A) (a : A) : Nat → A
  | 0 => G.id
  | n + 1 => G.op (power G a n) a

theorem power_zero (G : Group A) (a : A) :
    power G a 0 = G.id := by rfl

theorem power_succ (G : Group A) (a : A) (n : Nat) :
    power G a (n + 1) = G.op (power G a n) a := by rfl

theorem power_add (G : Group A) (a : A) (n m : Nat) :
    power G a (n + m) = G.op (power G a n) (power G a m) := by
  induction m with
  | zero => rw [Nat.add_zero, power_zero, G.id_right]
  | succ m ih =>
      rw [Nat.add_succ, power_succ, power_succ, ih, G.assoc]

theorem power_one (G : Group A) (a : A) : power G a 1 = a := by
  rw [power_succ, power_zero, G.id_left]

def productGroup (G : Group A) (H : Group B) : Group (A × B) where
  op x y := (G.op x.1 y.1, H.op x.2 y.2)
  id := (G.id, H.id)
  inv x := (G.inv x.1, H.inv x.2)
  assoc := by
    intro x y z
    ext
    · exact G.assoc x.1 y.1 z.1
    · exact H.assoc x.2 y.2 z.2
  id_left := by
    intro x
    ext
    · exact G.id_left x.1
    · exact H.id_left x.2
  id_right := by
    intro x
    ext
    · exact G.id_right x.1
    · exact H.id_right x.2
  inv_left := by
    intro x
    ext
    · exact G.inv_left x.1
    · exact H.inv_left x.2
  inv_right := by
    intro x
    ext
    · exact G.inv_right x.1
    · exact H.inv_right x.2

def twoElementGroup : Group Bool where
  op := Bool.xor
  id := false
  inv a := a
  assoc := by
    expand
    decide
  id_left := by
    expand
    decide
  id_right := by
    expand
    decide
  inv_left := by decide
  inv_right := by decide

theorem bool_power_three : power twoElementGroup true 3 = true := by rfl

theorem bool_power_four : power twoElementGroup true 4 = false := by rfl

def Permutation (A : Type) := { f : A → A // Bijective f }

@[ext] theorem permutation_ext {p q : Permutation A}
    (h : p.val = q.val) : p = q := by
  apply Subtype.ext
  exact h

def permutationIdentity (A : Type) : Permutation A :=
  { val := identity A, property := identity_bijective A }

def permutationCompose (p q : Permutation A) : Permutation A :=
  { val := compose p.val q.val
    property := by
      apply bijective_compose
      · exact q.property
      · exact p.property }

noncomputable def permutationInverse (p : Permutation A) : Permutation A :=
  { val := inverseMap p.val p.property
    property := inverseMap_bijective p.val p.property }

noncomputable def permutationGroup (A : Type) : Group (Permutation A) where
  op := permutationCompose
  id := permutationIdentity A
  inv := permutationInverse
  assoc := by
    intro p q r
    ext! x
    rfl
  id_left := by
    intro p
    ext! x
    rfl
  id_right := by
    intro p
    ext! x
    rfl
  inv_left := by
    intro p
    ext! x
    exact inverseMap_left p.val p.property x
  inv_right := by
    intro p
    ext! x
    exact inverseMap_spec p.val p.property x

theorem productGroup_abelian (G : Group A) (H : Group B)
    (hG : IsAbelian G) (hH : IsAbelian H) :
    IsAbelian (productGroup G H) := by
  intro x y
  ext
  · exact hG x.1 y.1
  · exact hH x.2 y.2

def swap [DecidableEq A] (a b x : A) : A :=
  if x = a then b else if x = b then a else x

theorem swap_left [DecidableEq A] (a b : A) : swap a b a = b := by
  rw [swap, ite_eq_left rfl]

theorem swap_right [DecidableEq A] (a b : A) (hba : b ≠ a) : swap a b b = a := by
  rw [swap, ite_eq_right hba, ite_eq_left rfl]

theorem swap_other [DecidableEq A] (a b x : A) (hxa : x ≠ a) (hxb : x ≠ b) :
    swap a b x = x := by
  rw [swap, ite_eq_right hxa, ite_eq_right hxb]

theorem swap_twice [DecidableEq A] (a b x : A) :
    swap a b (swap a b x) = x := by
  by_cases hxa : x = a
  · rw [hxa, swap_left]
    by_cases hba : b = a
    · rw [hba, swap_left]
    · rw [swap_right a b hba]
  · by_cases hxb : x = b
    · have hba : b ≠ a := by
        intro h
        apply hxa
        exact hxb.trans h
      rw [hxb, swap_right a b hba, swap_left]
    · rw [swap_other a b x hxa hxb, swap_other a b x hxa hxb]

theorem swap_bijective [DecidableEq A] (a b : A) : Bijective (swap a b) := by
  constructor
  · intro x y hxy
    calc
      x = swap a b (swap a b x) := by rw [swap_twice]
      _ = swap a b (swap a b y) := by rw [hxy]
      _ = y := by rw [swap_twice]
  · intro y
    exists (swap a b y)
    exact swap_twice a b y

def transposition01 : Permutation (Fin 3) :=
  { val := swap 0 1, property := swap_bijective 0 1 }

def transposition12 : Permutation (Fin 3) :=
  { val := swap 1 2, property := swap_bijective 1 2 }

theorem permutationGroup_three_not_abelian :
    ¬ IsAbelian (permutationGroup (Fin 3)) := by
  intro h
  -- 합성 순서를 바꾸었을 때 원소 0의 상이 달라진다.
  have hMaps := h transposition01 transposition12
  indisc at hMaps with hFunctions
  indisc (0 : Fin 3) at hFunctions with hZero
  indisc at hZero with hValues
  have hBad : (1 : Nat) = 2 := hValues
  contradiction

#print axioms inv_op
#print axioms power_add
#print axioms productGroup
#print axioms permutationGroup
#print axioms permutationGroup_three_not_abelian

end Course.Preparation
