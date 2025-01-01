inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
  induction h with
  | nil => exact Palindrome.nil
  | single a => exact Palindrome.single a
  | sandwich a h ih => simp; exact Palindrome.sandwich _ ih

theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := by
  induction h with
  | nil => rfl
  | single a => rfl
  | sandwich a h ih => simp [ih]

example (h : Palindrome as) : Palindrome as.reverse := by
  simp [reverse_eq_of_palindrome h, h]

def List.last : (as : List α) → as ≠ [] → α
  | [a],         _ => a
  | _::a₂:: as, _ => (a₂::as).last (by simp)

@[simp] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
  match as with
  | [] => contradiction
  | [a] => simp_all [last, dropLast]
  | a₁ :: a₂ :: as =>
    simp [last, dropLast]
    exact dropLast_append_last (as := a₂ :: as) (by simp)

theorem List.palindrome_ind (motive : List α → Prop)
    (h₁ : motive [])
    (h₂ : (a : α) → motive [a])
    (h₃ : (a b : α) → (as : List α) → motive as → motive ([a] ++ as ++ [b]))
    (as : List α)
    : motive as :=
  match as with
  | []  => h₁
  | [a] => h₂ a
  | a₁::a₂::as' =>
    have ih := palindrome_ind motive h₁ h₂ h₃ (a₂::as').dropLast
    have : [a₁] ++ (a₂::as').dropLast ++ [(a₂::as').last (by simp)] = a₁::a₂::as' := by simp
    this ▸ h₃ _ _ _ ih
termination_by as.length

theorem List.palindrome_of_eq_reverse (h : as.reverse = as) : Palindrome as := by
  induction as using palindrome_ind
  next   => exact Palindrome.nil
  next a => exact Palindrome.single a
  next a b as ih =>
    have : a = b := by simp_all
    subst this
    have : as.reverse = as := by simp_all
    exact Palindrome.sandwich a (ih this)

def List.isPalindrome [DecidableEq α] (as : List α) : Bool :=
    as.reverse = as

theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := by
  simp [isPalindrome]
  exact Iff.intro (fun h => palindrome_of_eq_reverse h) (fun h => reverse_eq_of_palindrome h)

#eval [1, 2, 1].isPalindrome
#eval [1, 2, 3, 1].isPalindrome

example : [1, 2, 1].isPalindrome := rfl
example : [1, 2, 2, 1].isPalindrome := rfl
example : ![1, 2, 3, 1].isPalindrome := rfl
