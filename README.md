
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
            

Theorem “Correctness of `isPrefixOf`”:
      xs = xs₀ ∧ zs = zs₀
    ⇒⁅  r := true ⍮
        while r ∧ xs ≠ 𝜖
          do
            if zs = 𝜖
            then
              r := false
            else
              r := (head xs = head zs) ⍮
              xs := tail xs ⍮
              zs := tail zs
            fi
          od
      ⁆
      (r ≡ xs₀ isPrefixOf zs₀)
Proof:
    xs = xs₀ ∧ zs = zs₀
  ⇒⟨ “Leibniz” ⟩
    xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀
  =⟨ “Identity of ∧” ⟩
    true ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀
  ⇒⁅ r := true ⁆⟨ “Assignment” with Substitution ⟩
    r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀
  ⇒⁅   while r ∧ xs ≠ 𝜖
         do
           if zs = 𝜖
           then
             r := false
           else
             r := (head xs = head zs) ⍮
             xs := tail xs ⍮
             zs := tail zs
           fi
         od
   ⁆⟨ “While” with Subproof:
        Using “Conditional”:
          Subproof:
              zs = 𝜖 ∧ r ∧ xs ≠ 𝜖 ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            =⟨ “Abbreviated replacement” ⟩
              zs = 𝜖 ∧ r ∧ xs ≠ 𝜖 ∧ (r ∧ xs isPrefixOf 𝜖 ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ “Weakening” ⟩
              xs ≠ 𝜖 ∧ (r ∧ xs isPrefixOf 𝜖 ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ Monotonicity with “Non-empty-sequence decomposition” ⟩
              xs = head xs ◃ tail xs ∧ (r ∧ xs isPrefixOf 𝜖 ≡ xs₀ isPrefixOf zs₀)
            =⟨ “Abbreviated replacement” ⟩
              xs = head xs ◃ tail xs ∧ (r ∧ (head xs ◃ tail xs) isPrefixOf 𝜖 ≡ xs₀ isPrefixOf zs₀)
            =⟨ “Definition of `isPrefixOf`”, “Zero of ∧” ⟩
              xs = head xs ◃ tail xs ∧ (false ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ “Weakening” ⟩
              false ≡ xs₀ isPrefixOf zs₀
            =⟨ “Zero of ∧” ⟩
              false ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀
            ⇒⁅ r := false ⁆⟨ “Assignment” with Substitution ⟩
              r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀
          Subproof:
              ¬ (zs = 𝜖) ∧ r ∧ xs ≠ 𝜖 ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            =⟨ “Definition of ≠”, “Identity of ≡”, “Definition of ≡” ⟩
              zs ≠ 𝜖 ∧ (r = true) ∧ xs ≠ 𝜖 ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            =⟨ “Abbreviated replacement”, “Identity of ∧” ⟩
              zs ≠ 𝜖 ∧ (r = true) ∧ xs ≠ 𝜖 ∧ (xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ “Weakening” ⟩
              zs ≠ 𝜖 ∧ xs ≠ 𝜖 ∧ (xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ Monotonicity with “Non-empty-sequence decomposition” ⟩
              (zs = head zs ◃ tail zs) ∧ xs ≠ 𝜖 ∧ (xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ Monotonicity with “Non-empty-sequence decomposition” ⟩
              (zs = head zs ◃ tail zs) ∧ (xs = head xs ◃ tail xs) ∧ (xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
            =⟨ “Abbreviated replacement” ⟩
              (zs = head zs ◃ tail zs) ∧ (xs = head xs ◃ tail xs) ∧ ((head xs ◃ tail xs) isPrefixOf (head zs ◃ tail zs) ≡ xs₀ isPrefixOf zs₀)
            ⇒⟨ “Weakening” ⟩
              (head xs ◃ tail xs) isPrefixOf (head zs ◃ tail zs) ≡ xs₀ isPrefixOf zs₀
            =⟨ “Definition of `isPrefixOf`” ⟩
              (head xs = head zs) ∧ (tail xs) isPrefixOf (tail zs) ≡ xs₀ isPrefixOf zs₀
            ⇒⁅ r := (head xs = head zs) ⁆⟨ “Assignment” with Substitution ⟩
              r ∧ (tail xs) isPrefixOf (tail zs) ≡ xs₀ isPrefixOf zs₀
            ⇒⁅ xs := tail xs ⁆⟨ “Assignment” with Substitution ⟩
              r ∧ xs isPrefixOf (tail zs) ≡ xs₀ isPrefixOf zs₀
            ⇒⁅ zs := tail zs ⁆⟨ “Assignment” with Substitution ⟩
              r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀
      ⟩
    ¬ (r ∧ xs ≠ 𝜖) ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
  =⟨ “De Morgan”, “Negation of ≠” ⟩
    (¬ r ∨ xs = 𝜖) ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
  =⟨ “Distributivity of ∧ over ∨” ⟩
    (¬ r ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)) ∨ (xs = 𝜖 ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀))
  ⇒⟨ Subproof:
       Using “Case analysis”:
         Subproof for `(¬ r ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)) ⇒ (r ≡ xs₀ isPrefixOf zs₀)`:
           By cases: `r ≡ true`, `r ≡ false`
             Completeness:
                 (r ≡ true) ∨ (r ≡ false)
               =⟨ “Distributivity of ∨ over ≡” ⟩
                 r ∨ r ≡ true ∨ r ≡ r ∨ false ≡ true ∨ false
               =⟨ “Idempotency of ∨”, “Zero of ∨”, “Identity of ∨”, “Identity of ≡” ⟩
                 true
             Case (1) `r ≡ true`:
                 ¬ r ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
               =⟨ Assumption (1), “Definition of `false`”, “Zero of ∧” ⟩
                 false
               ⇒⟨ “ex falso quodlibet” ⟩
                 r ≡ xs₀ isPrefixOf zs₀
             Case (2) `r ≡ false`:
                 ¬ r ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
               =⟨ Assumption (2), “Negation of `false`”, “Identity of ∧”, “Zero of ∧” ⟩
                 false ≡ xs₀ isPrefixOf zs₀
               =⟨ Assumption (2) ⟩
                 r ≡ xs₀ isPrefixOf zs₀
         Subproof for `(xs = 𝜖 ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)) ⇒ (r ≡ xs₀ isPrefixOf zs₀)`:
             xs = 𝜖 ∧ (r ∧ xs isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
           =⟨ “Abbreviated replacement” ⟩
             xs = 𝜖 ∧ (r ∧ 𝜖 isPrefixOf zs ≡ xs₀ isPrefixOf zs₀)
           =⟨ “Definition of `isPrefixOf`”, “Identity of ∧” ⟩
             xs = 𝜖 ∧ (r ≡ xs₀ isPrefixOf zs₀)
           ⇒⟨ “Weakening” ⟩
             r ≡ xs₀ isPrefixOf zs₀
     ⟩
     r ≡ xs₀ isPrefixOf zs₀
Theorem “Specification of `isPrefixOf`”:  xs isPrefixOf zs ≡ (∃ ys • xs ⌢ ys = zs)
Proof:
  By induction on `xs : Seq A`:
    Base case `𝜖 isPrefixOf zs ≡ (∃ ys • 𝜖 ⌢ ys = zs)`:
        𝜖 isPrefixOf zs ≡ (∃ ys • 𝜖 ⌢ ys = zs)
      ≡⟨ “Definition of `isPrefixOf`” ⟩
        true ≡ (∃ ys • 𝜖 ⌢ ys = zs)
      ≡⟨ “Left-identity of ⌢” ⟩
        true ≡ (∃ ys • ys = zs)
      ≡⟨ “Identity of ∧” ⟩
        true ≡ (∃ ys • ys = zs ∧ true)
      ≡⟨ “Trading for ∃” ⟩
        true ≡ (∃ ys ❙ ys = zs • true)
      ≡⟨ “One-point rule for ∃” ⟩
        true ≡ true[ys ≔ zs]
      ≡⟨ Substitution  ⟩
        true ≡ true — This is “Reflexivity of ≡”
    Induction step `∀ x : A • (x ◃ xs) isPrefixOf zs ≡ (∃ ys • (x ◃ xs) ⌢ ys = zs)`:
      For any `x : A`:
        By induction on `zs : Seq A`:
          Base case `(x ◃ xs) isPrefixOf 𝜖 ≡ (∃ ys • (x ◃ xs) ⌢ ys = 𝜖)`:
              (x ◃ xs) isPrefixOf 𝜖 ≡ (∃ ys • (x ◃ xs) ⌢ ys = 𝜖)
            ≡⟨ “Definition of `isPrefixOf`” ⟩
              false ≡ (∃ ys • (x ◃ xs) ⌢ ys = 𝜖)
            ≡⟨ “Mutual associativity of ◃ with ⌢” ⟩
              false ≡ (∃ ys • x ◃ (xs ⌢ ys) = 𝜖)
            ≡⟨ “Cons is not empty” ⟩
              false ≡ (∃ ys • false)
            ≡⟨ “False ∃ body”, “Reflexivity of ≡” ⟩
              true
          Induction step `∀ z : A • (x ◃ xs) isPrefixOf (z ◃ zs) ≡ (∃ ys • (x ◃ xs) ⌢ ys = z ◃ zs)`:
            For any `z : A`:
                (x ◃ xs) isPrefixOf (z ◃ zs) ≡ (∃ ys • (x ◃ xs) ⌢ ys = z ◃ zs)
              ≡⟨ “Definition of `isPrefixOf`” ⟩
                x = z ∧ xs isPrefixOf zs ≡ (∃ ys • (x ◃ xs) ⌢ ys = z ◃ zs)
              ≡⟨ Induction hypothesis ⟩
                x = z ∧ (∃ ys • xs ⌢ ys = zs) ≡ (∃ ys • (x ◃ xs) ⌢ ys = z ◃ zs)
              ≡⟨ “Mutual associativity of ◃ with ⌢” ⟩
                x = z ∧ (∃ ys • xs ⌢ ys = zs) ≡ (∃ ys • x ◃ (xs ⌢ ys) = z ◃ zs)
              ≡⟨ “Cancellation of ◃” ⟩
                x = z ∧ (∃ ys • xs ⌢ ys = zs) ≡ (∃ ys • x = z ∧ xs ⌢ ys = zs)
              ≡⟨ “Distributivity of ∧ over ∃” ⟩
                x = z ∧ (∃ ys • xs ⌢ ys = zs) ≡ x = z ∧ (∃ ys • xs ⌢ ys = zs)
              ≡⟨ “Reflexivity of ≡” ⟩
                true

Lemma “ExprV evaluation after substitution”:
  ∀ e • evalV s (substV v f e) = evalV (s ⊕′ ⟨v, evalV s f⟩) e
Proof:
  Using “Induction over `ExprV`”:
    Subproof for `∀ u • evalV s (substV v f (Var′ u)) = evalV (s ⊕′ ⟨v, evalV s f⟩) (Var′ u)`:
      For any `u`:
        By cases: `u = v`, `v ≠ u` ╍╍╍ There is two case for substV with `Var' v`
          Completeness: By “Definition of ≠”, “LEM”
          Case `u ≠ v`:
              evalV s (substV v f (Var′ u))
            =⟨ “Definition of `substV`” with assumption `u ≠ v` ⟩
              evalV s (Var′ u)
            =⟨ “Definition of `evalV`” ⟩
              s u
            =⟨ “Definition of function override” with assumption `v ≠ u` ⟩
              (s ⊕′ ⟨v, evalV s f⟩) u ╍╍╍ Axiom (x ≠ z ⇒ (f ⊕′ ⟨ x, y ⟩) z = f z)
            =⟨ “Definition of `evalV`” ⟩
              evalV (s ⊕′ ⟨v, evalV s f⟩) (Var′ u)
          Case `u = v`:
              evalV s (substV v f (Var′ u))
            =⟨ Assumption `u = v` ⟩
              evalV s (substV v f (Var′ v))
            =⟨ “Definition of `substV`” ⟩
              evalV s f
            =⟨ “Definition of function override” with assumption `u = v` ⟩
              (s ⊕′ ⟨v, evalV s f⟩) u
            =⟨ “Definition of `evalV`” ⟩
              evalV (s ⊕′ ⟨v, evalV s f⟩) (Var′ u)
    Subproof:
      For any `n`:
          evalV s (substV v f (Int′ n))
        =⟨ “Definition of `substV`” ⟩
          evalV s (Int′ n)
        =⟨ “Definition of `evalV`” ⟩
          n
        =⟨ “Definition of `evalV`” ⟩
          evalV (s ⊕′ ⟨v, evalV s f⟩) (Int′ n)
    Subproof:
      For any `e₁, e₂` satisfying “IndHyp”
            `evalV s (substV v f e₁) = evalV (s ⊕′ ⟨v, evalV s f⟩) e₁ ∧
             evalV s (substV v f e₂) = evalV (s ⊕′ ⟨v, evalV s f⟩) e₂`:
          evalV s (substV v f (e₁ +′ e₂))
        =⟨ “Definition of `substV`” ⟩
          evalV s (substV v f e₁ +′ substV v f e₂)
        =⟨ “Definition of `evalV`” ⟩
          evalV s (substV v f e₁) + evalV s (substV v f e₂)
        =⟨ Assumption “IndHyp” ⟩
          evalV (s ⊕′ ⟨v, evalV s f⟩) e₁ +
          evalV (s ⊕′ ⟨v, evalV s f⟩) e₂
        =⟨ “Definition of `evalV`” ⟩
          evalV (s ⊕′ ⟨v, evalV s f⟩) (e₁ +′ e₂)
    Subproof:
      For any `e₁, e₂` satisfying “IndHyp”
            `evalV s (substV v f e₁) = evalV (s ⊕′ ⟨v, evalV s f⟩) e₁ ∧
             evalV s (substV v f e₂) = evalV (s ⊕′ ⟨v, evalV s f⟩) e₂`:
          evalV s (substV v f (e₁ ·′ e₂))
        =⟨ “Definition of `substV`” ⟩
          evalV s (substV v f e₁ ·′ substV v f e₂)
        =⟨ “Definition of `evalV`” ⟩
          evalV s (substV v f e₁) · evalV s (substV v f e₂)
        =⟨ Assumption “IndHyp” ⟩
          evalV (s ⊕′ ⟨v, evalV s f⟩) e₁ ·
          evalV (s ⊕′ ⟨v, evalV s f⟩) e₂
        =⟨ “Definition of `evalV`” ⟩
          evalV (s ⊕′ ⟨v, evalV s f⟩) (e₁ ·′ e₂)

Derived inference rule “Conditional”:

      `B ∧′ P ⇒⁅ C₁ ⁆ Q`,   `¬′ B ∧′ P ⇒⁅ C₂ ⁆ Q`
    ⊦————————————————————————————————————————————
        `P ⇒⁅ if B then C₁ else C₂ fi ⁆ Q`

Proof:
  Assuming (C₁) `B ∧′ P ⇒⁅ C₁ ⁆ Q` and using with “Partial correctness”,
           (C₂) `¬′ B ∧′ P ⇒⁅ C₂ ⁆ Q` and using with “Partial correctness”:
      P ⇒⁅ if B then C₁ else C₂ fi ⁆ Q
    ≡⟨ “Partial correctness” ⟩
      ⟦ if B then C₁ else C₂ fi ⟧ ⦇ sat P ⦈ ⊆ sat Q
    ≡⟨ “Conjunction on `Expr𝔹`”, “Negation on `Expr𝔹`” ⟩
      ⟦ while B do C od ⟧ ⦇ sat Q ⦈ ⊆ ~ (sat B) ∩ sat Q
    =⟨ “Relational image under ⨾” ⟩
       ⟦ C₂ ⟧ ⦇ (⟦ C₁ ⟧ ⦇ sat P ⦈) ⦈ ⊆ sat R
    ⇐⟨ Monotonicity of  with Assumption (C₁) ⟩
       ⟦ C₂ ⟧ ⦇ sat Q ⦈ ⊆ sat R
    ≡⟨ Assumption (C₂) ⟩
       true

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
