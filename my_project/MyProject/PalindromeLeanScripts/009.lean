

    -- Inductive definition for Palindrome
    inductive Palindrome : List α → Prop where
      | nil      : Palindrome []
      | single   : (a : α) → Palindrome [a]
      | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

    -- Prove that the reverse of a palindrome is a palindrome
    theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
      induction h with
      | nil => exact Palindrome.nil
      | single a => exact Palindrome.single a
      | sandwich a h ih => simp; exact Palindrome.sandwich _ ih

    -- Prove that if a list is a palindrome, its reverse is equal to itself
    theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := by
      induction h with
      | nil => rfl
      | single a => rfl
      | sandwich a h ih => simp [ih]

    -- Example using reverse_eq_of_palindrome
    example (h : Palindrome as) : Palindrome as.reverse := by
      simp [reverse_eq_of_palindrome h, h]

    -- Function to find the last element of a non-empty list
    def List.last : (as : List α) → as ≠ [] → α
      | [a],         _ => a
      | _::a₂::as, _ => (a₂::as).last (by simp)

    -- Theorem for appending the last element back to the list
    @[simp] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
      match as with
      | [] => contradiction
      | [a] => simp_all [last, dropLast]
      | a₁ :: a₂ :: as =>
        simp [last, dropLast]
        exact dropLast_append_last (as := a₂ :: as) (by simp)

    -- Auxiliary induction principle for lists
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

    -- Prove that if a list is equal to its reverse, it is a palindrome
    theorem List.palindrome_of_eq_reverse (h : as.reverse = as) : Palindrome as := by
      induction as using palindrome_ind
      next   => exact Palindrome.nil
      next a => exact Palindrome.single a
      next a b as ih =>
        have : a = b := by simp_all
        subst this
        have : as.reverse = as := by simp_all
        exact Palindrome.sandwich a (ih this)

    -- Function to check if a list is a palindrome
    def List.isPalindrome [DecidableEq α] (as : List α) : Bool :=
        as.reverse = as

    -- Prove the correctness of isPalindrome
    theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := by
      simp [isPalindrome]
      exact Iff.intro (fun h => palindrome_of_eq_reverse h) (fun h => reverse_eq_of_palindrome h)

    -- Evaluate the test case
    #eval [2, 2, 2, 2].isPalindrome ↔ True
    