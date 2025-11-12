“Set inclusion” ⊆ 
“Set extensionality” =
Mutual implication ≡
Induction over ℕ 
Mutual inclusion =
Relation extensionality = 
Relation inclusion = 
Theorem “M2.2”:
      m = m₀ ∧ n = n₀
    ⇒⁅  while n ≠ 0
          do
            n := n - 1 ⍮
            m := m - 1
          od
      ⁆
      m = m₀ - n₀
Proof:
    m = m₀ ∧ n = n₀   ╍╍╍  Precondition
  ≡⟨ “Cancellation of +”, “Subtraction” ⟩
    m - n = m₀ - n ∧ n = n₀
  ≡⟨ “Symmetry of ∧” ⟩
    n = n₀ ∧ m - n = m₀ - n
  ≡⟨ Substitution ⟩
    n = n₀ ∧ (m - n = m₀ - z)[z ≔ n]
  ≡⟨ “Replacement”, Substitution ⟩
    n = n₀ ∧ (m - n = m₀ - n₀)
  ⇒⟨ “Weakening” ⟩
    m - n = m₀ - n₀
  ⇒⁅ while n ≠ 0 do
        n := n - 1 ⍮
        m := m - 1
      od ⁆⟨ “While” with subproof:
          n ≠ 0 ∧ m - n = m₀ - n₀  ╍╍╍  Loop condition and invariant
        ⇒ ⟨ “Weakening” ⟩
          m - n = m₀ - n₀
        ≡⟨ “Identity of +” ⟩
          m - n + 0 = m₀ - n₀
        ≡⟨ Fact `1 - 1 = 0` ⟩
          m - n + (1 - 1) = m₀ - n₀
        ≡⟨ “Subtraction” ⟩
          m + - n + (1 + - 1) = m₀ - n₀
        ≡⟨ “Symmetry of +” ⟩
          m + 1 + - n + - 1 = m₀ - n₀
        ≡⟨ “Subtraction” ⟩
          m + 1 - n - 1 = m₀ - n₀
        ≡⟨ “Subtraction of addition”⟩
          (m + 1) - (n + 1) = m₀ - n₀
        ≡⟨ (15.26) ⟩
          (m - 1) - (n - 1) = m₀ - n₀
        ⇒⁅ n := n - 1 ⁆⟨ “Assignment” with substitution ⟩
          (m - 1) - n = m₀ - n₀
        ⇒⁅ m := m - 1 ⁆⟨ “Assignment” with substitution ⟩
          m - n = m₀ - n₀
    ⟩
    ¬ (n ≠ 0) ∧ m - n = m₀ - n₀  ╍╍╍ Negated loop condition, and invariant
  =⟨ “Definition of ≠” ⟩
    ¬ ¬ (n = 0) ∧ m - n = m₀ - n₀
  =⟨ “Double negation” ⟩
    n = 0 ∧ m - n = m₀ - n₀
  =⟨ Substitution ⟩
    n = 0 ∧ (m - z = m₀ - n₀)[z ≔ n]
  =⟨ “Replacement” with Substitution ⟩
    n = 0 ∧ (m - 0 = m₀ - n₀)
  ⇒⟨ “Weakening” ⟩
    m - 0 = m₀ - n₀
  =⟨ “Right-identity of -” ⟩
    m = m₀ - n₀

Theorem “M2.3b”: Ran (R ⨾ S) = Ran (Ran R ◁ S)
Proof:
  Using “Set extensionality”:
    For any `y`:
        y ∈ Ran (R ⨾ S) 
      =⟨“Membership in `Ran`”⟩ 
        ∃ x • x ⦗ R ⨾ S ⦘ y 
      =⟨ “Relation composition” ⟩ 
        ∃ x • (∃ b • x ⦗ R ⦘ b ∧ b ⦗ S ⦘ y ) 
      =⟨ “Trading for ∃” ⟩ 
        ∃ x • (∃ b ❙ x ⦗ R ⦘ b • b ⦗ S ⦘ y )
      =⟨ “Nesting for ∃” ⟩ 
        ∃ x, b ❙ x ⦗ R ⦘ b • b ⦗ S ⦘ y 
      =⟨ “Dummy list permutation for ∃” ⟩ 
        ∃ b, x ❙ x ⦗ R ⦘ b • b ⦗ S ⦘ y 
      =⟨ “Nesting for ∃” ⟩ 
        ∃ b • (∃ x ❙ x ⦗ R ⦘ b • b ⦗ S ⦘ y)
      =⟨ (9.22) ⟩ 
        ∃ b • ((b ⦗ S ⦘ y) ∧ (∃ x  •  x ⦗ R ⦘ b))
      =⟨ “Membership in `Ran`” ⟩ 
        ∃ b • ((b ⦗ S ⦘ y) ∧ (b ∈ Ran R))
      =⟨ “Relationship via ◁” ⟩ 
        ∃ b • (b ⦗ Ran R ◁ S ⦘ y)
      =⟨ “Membership in `Ran`” ⟩ 
        y ∈ Ran (Ran R ◁ S )

Theorem “M2.3a”:   A ◁ R = id A ⨾ R
Proof:
  Using “Relation extensionality”:
    For any `x, y`:
        x ⦗ A ◁ R ⦘ y
      ≡⟨ “Domain restriction” ⟩
        x ∈ A ∧ x ⦗ R ⦘ y
      ≡⟨ “Identity of ⨾” ⟩
        x ∈ A ∧ x ⦗ 𝕀 ⨾ R ⦘ y
      ≡⟨ “Relation composition” ⟩
        x ∈ A ∧ (∃ b • x ⦗ 𝕀 ⦘ b ∧ b ⦗ R ⦘ y )
      ≡⟨ “Relationship via 𝕀” ⟩
        x ∈ A ∧ (∃ b • x = b ∧ b ⦗ R ⦘ y )
      ≡⟨ “Trading for ∃” ⟩
        x ∈ A ∧ (∃ b ❙ x = b • b ⦗ R ⦘ y )
      ≡⟨ “Distributivity of ∧ over ∃” ⟩
        (∃ b ❙ x = b • x ∈ A ∧ b ⦗ R ⦘ y)
      ≡⟨ “Trading for ∃” ⟩
        (∃ b • x = b ∧ x ∈ A ∧ b ⦗ R ⦘ y)
      ≡⟨ “Associativity of ∧” ⟩
        (∃ b • x = b ∧ x ∈ A ∧ b ⦗ R ⦘ y)
      ≡⟨ Substitution ⟩
        ∃ b • x = b ∧ (g ∈ A ∧ b ⦗ R ⦘ y)[g ≔ x]
      ≡⟨ “Replacement” with Substitution ⟩
        ∃ b • x = b ∧ b ∈ A ∧ b ⦗ R ⦘ y
      ≡⟨ “Replacement” with Substitution ⟩
        ∃ b • x = b ∧ b ∈ A ∧ b ⦗ R ⦘ y
      ≡⟨ “Idempotency of ∧” ⟩
        ∃ b • x = b ∈ A ∧ b ⦗ R ⦘ y
      ≡⟨ “Relationship via `id`” ⟩
        ∃ b • x ⦗ id A ⦘ b ∧ b ⦗ R ⦘ y
      ≡⟨ “Relation composition” ⟩
        x ⦗ id A ⨾ R ⦘ y

Theorem “Predecessor of non-zero”:
    n ≠ 0  ≡  suc (pred n) = n
Proof:
  By induction on `n : ℕ`:
    Base case `0 ≠ 0  ≡  suc (pred 0) = 0`:
        suc (pred 0) = 0
      =⟨ “Predecessor of zero” ⟩
        suc 0 = 0
      =⟨ “Zero is not successor” ⟩
        false
      =⟨ “Irreflexivity of ≠” ⟩
        0 ≠ 0    
    Induction step `suc n ≠ 0  ≡  suc (pred (suc n)) = suc n`:
        suc n ≠ 0  ≡  suc (pred (suc n)) = suc n
      = ⟨ “Predecessor of successor” ⟩
        suc n ≠ 0  ≡  suc n = suc n
      = ⟨ “Reflexivity of =” ⟩
        suc n ≠ 0 ≡ true
      =⟨ “Definition of ≠” ⟩
        ¬ (suc n = 0) ≡ true
      =⟨ “Zero is not successor” ⟩
        ¬ (false) ≡ true
      =⟨ “Negation of `false`” ⟩
        true ≡ true
      =⟨ “Identity of ≡” ⟩
        true

Theorem “M2.1b”:
    reflexive E  ∧  univalent F  ∧  E ⊆ F ⨾ F ˘
  ⇒ E ⨾ F = F
Proof:
  Assuming `reflexive E` and using with “Definition of univalence”,
           `univalent F` and using with “Definition of univalence”,
           `E ⊆ F ⨾ F ˘`:
    Using “Mutual inclusion”:
      Subproof for `E ⨾ F ⊆ F`:
            E ⨾ F
        ⊆⟨ “Monotonicity of ⨾” with Assumption `E ⊆ F ⨾ F ˘` ⟩
            (F ⨾ F ˘) ⨾ F
        =⟨ “Associativity of ⨾” ⟩
            F ⨾ (F ˘ ⨾ F)
        ⊆⟨ “Monotonicity of ⨾” with Assumption `univalent F` ⟩
            F ⨾ 𝕀
        =⟨ “Identity of ⨾” ⟩
            F
      Subproof for `F ⊆ E ⨾ F`:
        Using “Relation inclusion”:
          Subproof for `∀ x • (∀ y • x ⦗ F ⦘ y ⇒ x ⦗ E ⨾ F ⦘ y )`:
            For any `x`, `y`:
                x ⦗ F ⦘ y ⇒ x ⦗ E ⨾ F ⦘ y
              =⟨ “Relation composition” ⟩
                x ⦗ F ⦘ y ⇒ (∃ b • x ⦗ E ⦘ b ∧ b ⦗ F ⦘ y )
              =⟨ “Relation composition” ⟩
                x ⦗ F ⦘ y ⇒ (∃ b • x ⦗ E ⦘ b ∧ b ⦗ F ⦘ y )
              ⇒⟨ ?, “Trading for ∃” ⟩
                ∃ z • x ⦗ E ⦘ z ∧ z ⦗ F ⦘ y
              ⇒⟨ “Relation composition” ⟩
                x ⦗ E ⨾ F ⦘ y
                
Theorem “M2.1a”: R = R ⨾ (𝕀 ∩ R ˘ ⨾ R)
Proof:
  Using “Mutual inclusion”:
    Subproof for `R ⊆ R ⨾ (𝕀 ∩ R ˘ ⨾ R)`:
        R ⨾ (𝕀 ∩ R ˘ ⨾ R)
      ⊇⟨“Modal rule”⟩
        (R) ⨾ 𝕀  ∩ R
      =⟨“Identity of ⨾”⟩
        (R) ⨾ 𝕀  ∩ R ⨾ 𝕀
      =⟨“Idempotency of ∩”⟩
        (R) ⨾ 𝕀 
      =⟨“Identity of ⨾”⟩
        R
    Subproof for `R ⨾ (𝕀 ∩ R ˘ ⨾ R)  ⊆ R `:
        R ⨾ (𝕀 ∩ R ˘ ⨾ R)
      ⊆⟨ “Sub-distributivity of ⨾ over ∩” ⟩
        R ⨾ 𝕀 ∩ R ⨾ (R ˘ ⨾ R)
      =⟨ “Identity of ⨾” ⟩
        R ∩ (R ⨾ R ˘ ⨾ R)
      =⟨ “Set inclusion via ∩” with “Co-difunctionality” ⟩
        R
        
Theorem (11.6) “Mathematical formulation of set comprehension”:
     {x ❙ P • E } = { y ❙ (∃ x ❙ P • y = E) }
Proof:
  Using “Set extensionality”:
    Subproof for `∀ e  •  e ∈ {x ❙ P • E }  ≡  e ∈ { y ❙ (∃ x ❙ P • y = E) }`:
      For any `e`:
          e ∈ { y ❙ (∃ x ❙ P • y = E) }
        ≡⟨“Simple Membership”⟩
          (∃ x ❙ P • y = E)[y ≔ e]
        ≡⟨ Substitution ⟩
          (∃ x ❙ P • e = E)
        ≡⟨ “Set membership” ⟩
          e ∈ {x ❙ P • E }
Theorem (Ex6.5.1): x < 2  ∧  5 < y  ⇒  x < 3 < y
Proof:
    x < 2  ∧  5 < y
  ⇒⟨ “Monotonicity of ∧” with 
     “Right-monotonicity of <” with Fact `2 ≤ 3`  ⟩
    x < 3  ∧  5 < y
  ⇒⟨ “Monotonicity of ∧” with 
     “Left-antitonicity of <” with Fact `3 ≤ 5` ⟩
    x < 3 < y

Theorem (Ex6.5.2): (x < 2  ⇒  5 ≤ y)  ⇒  (x < 1 ⇒ 4 ≤ y)
Proof:
    x < 2  ⇒  5 ≤ y
  ⇒⟨ “Antitonicity of ⇒” with
     “Right-monotonicity of <” with Fact `1 ≤ 2` ⟩
    x < 1  ⇒  5 ≤ y
  ⇒⟨ “Monotonicity of ⇒” with
     “Left-antitonicity of ≤” with Fact `4 ≤ 5` ⟩
    x < 1  ⇒  4 ≤ y

        
Theorem “Symmetry of +”: ∀ m • ∀ n • m + n = n + m
Proof:
  Using “Induction over ℕ”:
    Subproof:
      For any `n : ℕ`:
          0 + n
        =⟨ “Definition of +” ⟩
          n
        =⟨ “Right-identity of +”  ⟩
          n + 0
    Subproof:
      For any `m : ℕ` satisfying “IndHyp” `∀ n • m + n = n + m`:
        For any `n : ℕ`:
            (m + 1) + n
          =⟨ “Definition of +” ⟩
            (m + n) + 1
          =⟨ Assumption “IndHyp” ⟩
            (n + m) + 1
          =⟨ “Definition of +” ⟩
            (n + 1) + m
          =⟨ “Shifting successor over +” ⟩
            n + (m + 1)
Theorem “Univalence of composition”:
     univalent R ⇒ univalent S ⇒ univalent (R ⨾ S)
Proof:
  Assuming `univalent R` and using with “Definition of univalence”,
           `univalent S` and using with “Definition of univalence”:
    Using “Definition of univalence”:
        (R ⨾ S) ˘ ⨾ (R ⨾ S)
      =⟨ “Converse of ⨾” ⟩
        (S ˘ ⨾ R ˘) ⨾ R ⨾ S
      =⟨ “Associativity of ⨾” ⟩
        S ˘ ⨾ (R ˘ ⨾ R) ⨾ S
      ⊆⟨ “Monotonicity of ⨾” with “Monotonicity of ⨾” with
         Assumption `univalent R` ⟩
        S ˘ ⨾ 𝕀 ⨾ S
      =⟨ “Identity of ⨾” ⟩
        S ˘ ⨾ S
      ⊆⟨ Assumption `univalent S` ⟩
        𝕀
        
Theorem “Squaring”:
      true
    ⇒⁅  i := 0 ⍮
        s := 0 ⍮
        d := 1 ⍮
        while i ≠ n
          do
            s := s + d ⍮
            d := d + 2 ⍮
            i := i + 1
          od
       ⁆ s = n · n
Proof:
    true   ╍╍╍  Precondition
  ≡⟨ “Idempotency of ∧” ⟩
    true ∧ true 
  ≡⟨ Fact `1 = 0 + 0 + 1`, Fact `0 = 0 · 0` ⟩
    1 = 0 + 0 + 1 ∧ 0 = 0 · 0
  ⇒⁅ i := 0 ⁆⟨ “Assignment” with substitution ⟩
    1 = i + i + 1 ∧ 0 = i · i
  ⇒⁅ s := 0 ⁆⟨ “Assignment” with substitution ⟩
    1 = i + i + 1 ∧ s = i · i
  ⇒⁅ d := 1 ⁆⟨ “Assignment” with substitution ⟩
    d = i + i + 1 ∧ s = i · i      ╍╍╍  Invariant
  ⇒⁅ while i ≠ n do
        s := s + d ⍮
        d := d + 2 ⍮
        i := i + 1
      od ⁆⟨ “While” with subproof:
          i ≠ n ∧ d = i + i + 1 ∧ s = i · i  ╍╍╍  Loop condition and invariant
        ⇒⟨ “Weakening” (3.76b) ⟩
          d = i + i + 1 ∧ s = i · i
        =⟨ “Cancellation of +” ⟩   
          d = i + i + 1 ∧ s + d = i · i + d
        =⟨ Substitution ⟩ 
          d = i + i + 1 ∧ (s + d = i · i + z)[z ≔ d]
        ≡⟨ “Replacement” (3.84a) ⟩ 
          d = i + i + 1 ∧ (s + d = i · i + z)[z ≔ i + i + 1]
        ⇒⁅ s := s + d ⁆⟨ “Assignment” with substitution ⟩
          d = i + i + 1 ∧ s = i · i + i + i + 1
        ≡⟨ “Cancellation of +” ⟩
          d + 2 = i + i + 1 + 2 ∧ s = i · i + i + i + 1
        ⇒⁅ d := d + 2 ⁆⟨ “Assignment” with substitution ⟩
          d = i + i + 1 + 2 ∧ s = i · i + i + i + 1
        ≡⟨ “Distributivity of · over +”, “Identity of ·” ⟩
          d = i + i + 1 + 2 ∧ s = (i + 1) · (i + 1)
        ⇒⁅ i := i + 1 ⁆⟨ “Assignment” with substitution
                         and Fact `1 + 1 = 2` ⟩
          d = i + i + 1 ∧ s = i · i   ╍╍╍  Invariant
    ⟩
    ¬ (i ≠ n) ∧ d = i + i + 1 ∧ s = i · i  ╍╍╍ Negated loop condition, and invariant
  ≡⟨ “Definition of ≠”, “Double negation” ⟩
    (i = n) ∧ d = i + i + 1 ∧ s = i · i
  ⇒⟨ “Weakening”  (3.76b) ⟩
    (i = n) ∧ s = i · i
  =⟨ Substitution ⟩
     i = n  ∧ (s = z · z)[z ≔ i]
  =⟨ “Replacement” (3.84a) , Substitution ⟩
     i = n  ∧ s = n · n
  ⇒⟨ “Weakening” (3.76b) ⟩ 
    s = n · n    ╍╍╍  Postcondition

Theorem “Summing up”:
      true
    ⇒⁅  s := 0 ⍮
        i := 0 ⍮
        while i ≠ n
          do
            s := s + f i ⍮
            i := i + 1
          od
      ⁆
      s = ∑ j : ℕ ❙ j < n • f j
Proof:
    true
  =⟨ “Reflexivity of =” ⟩ 
    0 = 0
  =⟨ “Nothing is less than zero” , “Empty range for ∑” ⟩ 
    0 = ∑ j : ℕ ❙ j < 0 • f j
  ⇒⁅ s := 0 ⁆⟨ “Assignment” with substitution ⟩
    s = ∑ j : ℕ ❙ j < 0 • f j
  ⇒⁅ i := 0 ⁆⟨ “Assignment” with substitution ⟩ 
    s = ∑ j : ℕ ❙ j < i • f j
  ⇒⁅ while i ≠ n do
        s := s + f i ⍮
        i := i + 1
      od ⁆⟨ “While” with subproof:
          i ≠ n ∧ s = ∑ j : ℕ ❙ j < i • f j  ╍╍╍  Loop condition and invariant
        ⇒⟨ “Weakening” (3.76b) ⟩ 
          s = (∑ j : ℕ ❙ j < i • f j) 
        =⟨ Substitution, “Cancellation of +” ⟩ 
          s + f i = (∑ j : ℕ ❙ j < i • f j) + (f j)[j ≔ i]
        =⟨ “Split off term from ∑ at top” ⟩
          s + f i = ∑ j : ℕ ❙ j < suc i • f j
        =⟨ “Successor” ⟩    
          s + f i = ∑ j : ℕ ❙ j < i + 1 • f j
        ⇒⁅ s := s + f i ⁆⟨ “Assignment” with substitution ⟩
          s = ∑ j : ℕ ❙ j < i + 1 • f j       
        ⇒⁅ i := i + 1 ⁆⟨ “Assignment” with substitution ⟩
          s = ∑ j : ℕ ❙ j < i • f j   ╍╍╍  Invariant
    ⟩ 
    ¬ (i ≠ n) ∧ s = ∑ j : ℕ ❙ j < i • f j
  =⟨ “Definition of ≠”, “Double negation” ⟩
    (i = n) ∧ s = ∑ j : ℕ ❙ j < i • f j 
  =⟨ Substitution ⟩
    (i = n) ∧ (s = ∑ j : ℕ ❙ j < z • f j)[z ≔ i]
  =⟨ “Replacement” (3.84a) , Substitution ⟩
    (i = n) ∧ (s = ∑ j : ℕ ❙ j < n • f j)
  ⇒⟨ “Weakening” (3.76b) ⟩
    s = ∑ j : ℕ ❙ j < n • f j 
