Theorem (15.27): (a - b) · (c - d) = (a · c + b · d) - (a · d + b · c)
Proof:
    (a - b) · (c - d)
  = ⟨ “Subtraction” ⟩ 
    (a + (- b)) · (c - d)
  = ⟨ “Distributivity of · over +” ⟩
     a · (c - d) + (- b) · (c - d) 
  = ⟨ (15.20) ⟩
     a · (c - d) + (- 1) · b · (c - d) 
  = ⟨ “Associativity of ·” ⟩
     a · (c - d) + (- 1) · (b · (c - d))
  = ⟨ (15.20) ⟩
     a · (c - d) + (- (b · (c - d)))
  = ⟨ “Subtraction” ⟩
     a · (c + (- d)) - b · (c + (- d))
  = ⟨ “Distributivity of · over +” ⟩
     a · c + a · (- d) - (b · c + b · (- d))
  = ⟨ (15.22) ⟩
     a · c + (- (a · d)) - (b · c + (- (b · d)))
  = ⟨ “Subtraction” ⟩
     a · c - a · d - (b · c - b · d)
  = ⟨ (15.26) ⟩
     (a · c + b · d) - (a · d + b · c)

 Theorem (15.29) “Distributivity of · over -”:
    (a - b) · c = a · c - b · c
Proof:
    (a - b) · c
  =⟨ “Subtraction” ⟩
    (a + (- b)) · c
  =⟨ “Distributivity of · over +” ⟩
    a · c + (- b) · c
  =⟨ (15.20) ⟩
    a · c + (- 1) · b · c
  =⟨ “Associativity of ·” ⟩
    a · c + (- 1) · (b · c)
  =⟨ (15.20) ⟩
    a · c + (- (b · c))
  =⟨ “Subtraction” ⟩
    a · c - b · c

 Calculation:
    (2 · x + 3 · y)[x, y ≔ y + 1, (x + 4)[x ≔ y + 5]]
  =⟨ Substitution ⟩
    (2 · x + 3 · y)[x, y ≔ y + 1, y + 5 + 4]
  =⟨ Evaluation ⟩
    (2 · x + 3 · y)[x, y ≔ y + 1, y + 9]
  =⟨ Substitution ⟩
    2 · (y + 1) + 3 · (y + 9)
  =⟨ “Distributivity of · over +” ⟩
    2 · y + 2 · 1 + 3 · y + 3 · 9
  =⟨ “Symmetry of +” ⟩
    3 · y + 2 · y + 2 · 1  + 3 · 9
  =⟨ “Associativity of +” ⟩
    3 · y + 2 · y + (2 · 1  + 3 · 9)
  =⟨ “Distributivity of · over +” ⟩
    (3 + 2) · y + (2 · 1  + 3 · 9)
  =⟨ Evaluation ⟩
    5 · y + (2  + 27)
  =⟨ Evaluation ⟩
    5 · y + 29

  Lemma (Ex2.6d):       s
                 ⇒⁅  q := (¬ p ∧ s)
                   ⍮ r := (p ∧ s)
                   ⁆
                      (p ∨ q) ∧ (¬ p ∨ r)
Proof:
    s
  ≡⟨ “Identity of ∨” ⟩
    false ∨ s
  ≡⟨ “Contradiction” ⟩
    (p ∧ ¬ p) ∨ s
  ≡⟨ “Distributivity of ∨ over ∧” ⟩
    (p ∨ s) ∧ (¬ p ∨ s)
  ≡⟨ “Identity of ∧”  ⟩
    (true ∧ (p ∨ s)) ∧ (true ∧ (¬ p ∨ s))
  ≡⟨ “LEM” ⟩
    ((p ∨ ¬ p) ∧ (p ∨ s)) ∧ ((p ∨ ¬ p) ∧ (¬ p ∨ s))
  ≡⟨ “Symmetry of ∨” ⟩
    ((p ∨ ¬ p) ∧ (p ∨ s)) ∧ ((¬ p ∨ p) ∧ (¬ p ∨ s))
  ≡⟨ “Distributivity of ∨ over ∧” ⟩
    (p ∨ (¬ p ∧ s)) ∧ (¬ p ∨ (p ∧ s))
  ≡⟨ Substitution ⟩
    ((p ∨ q) ∧ (¬ p ∨ (p ∧ s)))[q ≔ (¬ p ∧ s)]
  ⇒⁅ q := (¬ p ∧ s) ⁆ ⟨ “Assignment” ⟩
    (p ∨ q) ∧ (¬ p ∨ (p ∧ s))
  ≡⟨ Substitution ⟩
    ((p ∨ q) ∧ (¬ p ∨ r))[r ≔ (p ∧ s)]
  ⇒⁅ r := (p ∧ s) ⁆ ⟨ “Assignment” ⟩
    (p ∨ q) ∧ (¬ p ∨ r)

Theorem (3.31) “Distributivity of ∨ over ∨”: p ∨ (q ∨ r) ≡ (p ∨ q) ∨ (p ∨ r)
Proof:
    (p ∨ q) ∨ (p ∨ r)
  =⟨ “Associativity of ∨” ⟩
    (p ∨ q ∨ p) ∨ r
  =⟨ “Associativity of ∨” ⟩
    ((p ∨ p) ∨ q) ∨ r
  =⟨ “Idempotency of ∨” ⟩
    (p ∨ q) ∨ r
  =⟨ “Associativity of ∨” ⟩
    p ∨ (q ∨ r)
 
Theorem (3.32): p ∨ q ≡ p ∨ ¬ q ≡ p
Proof:
    p ∨ q ≡ p ∨ ¬ q
  =⟨ “Distributivity of ∨ over ≡” ⟩
    p ∨ (q ≡ ¬ q)
  =⟨ “Commutativity of ¬ with ≡” ⟩
    p ∨ ¬ (q ≡ q)
  =⟨ “Identity of ≡” ⟩
    p ∨ ¬ true
  =⟨ “Definition of `false`” ⟩
    p ∨ false
  =⟨ “Identity of ∨” ⟩
    p 

Theorem (3.55): (p ∧ q) ∧ r ≡ p ≡ q ≡ r ≡ p ∨ q ≡ q ∨ r ≡ r ∨ p ≡ p ∨ q ∨ r
Proof:
    (p ∧ q) ∧ r
  ≡ ⟨ “Golden rule” ⟩ 
    (p ≡ q ≡ p ∨ q) ∧ r
  ≡ ⟨ “Golden rule” with `p, q ≔ (p ≡ q ≡ p ∨ q), r` ⟩ 
    (p ≡ q ≡ p ∨ q) ≡ r ≡ (p ≡ q ≡ p ∨ q) ∨ r
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩ 
    (p ≡ q ≡ p ∨ q) ≡ r ≡ p ∨ r ≡ q ∨ r ≡ p ∨ q ∨ r 
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩ 
    (p ≡ q ≡ p ∨ q) ≡ r ≡ p ∨ r ≡ q ∨ r ≡ p ∨ q ∨ r 

Theorem (3.44) (3.44b) “Absorption”: p ∨ (¬ p ∧ q) ≡ p ∨ q
Proof:
    p ∨ q 
  =⟨ (3.32) ⟩
    p ∨ ¬ q ≡ p 
  =⟨ “Idempotency of ∨” ⟩
    p ∨ ¬ q ≡ p ∨ p
  =⟨ “Distributivity of ∨ over ≡” ⟩
    p ∨ (p ≡ ¬ q)
  =⟨ “¬ connection” ⟩
    p ∨ (¬ p ≡ q)
  =⟨ “Golden rule” ⟩
    p ∨ ((¬ p ∨ q) ≡ (¬ p ∧ q))
  =⟨ “Distributivity of ∨ over ≡”  ⟩
    p ∨ (¬ p ∨ q) ≡ p ∨ (¬ p ∧ q)
  =⟨ “Associativity of ∨”  ⟩
    (p ∨ ¬ p) ∨ q ≡ p ∨ (¬ p ∧ q)
  =⟨ “LEM” ⟩
    true ∨  q ≡ p ∨ (¬ p ∧ q)
  =⟨ “Zero of ∨” ⟩
    true ≡ p ∨ (¬ p ∧ q)
  =⟨ “Identity of ≡” ⟩
    p ∨ (¬ p ∧ q)

Theorem (3.62): p ⇒ (q ≡ r) ≡ p ∧ q ≡ p ∧ r
Proof:
    p ⇒ (q ≡ r)
  =⟨ “Definition of ⇒” ⟩
    ¬ p ∨ (q ≡ r)
  =⟨ “Distributivity of ∨ over ≡” ⟩
    ¬ p ∨ q ≡ ¬ p ∨ r
  =⟨ (3.32) ⟩
    (q ∨ p ≡ q) ≡ (r ∨ p ≡ r)
  =⟨ “Golden rule” ⟩
    q ∧ p ≡ p ≡ p ≡ p ∧ r
  =⟨ “Identity of ≡” ⟩
    q ∧ p ≡ true ≡ p ∧ r
  =⟨ “Identity of ≡” ⟩
    p ∧ q ≡ p ∧ r

Theorem (3.82) (3.82b) “Transitivity of ⇒”: (p ≡ q) ∧ (q ⇒ r) ⇒ (p ⇒ r)
Proof: 
    (p ≡ q) ∧ (q ⇒ r) ⇒ (p ⇒ r)
  = ⟨ “Definition of ⇒” (3.59) ⟩
    ¬ ((p ≡ q) ∧ (q ⇒ r)) ∨ (p ⇒ r)
  = ⟨ “De Morgan” ⟩
    ¬ (p ≡ q) ∨ ¬ (q ⇒ r) ∨ (p ⇒ r)
  = ⟨ “Definition of ⇒” (3.59) ⟩
    ¬ (p ≡ q) ∨ ¬ (¬ q ∨ r) ∨ (¬ p ∨ r)
  = ⟨ “De Morgan” ⟩
    ¬ (p ≡ q) ∨ (¬ ¬ q ∧ ¬ r) ∨ ¬ p ∨ r
  = ⟨ “Symmetry of ∨” ⟩
    ¬ (p ≡ q) ∨ (¬ ¬ q ∧ ¬ r) ∨ r ∨ ¬ p
  = ⟨ “Absorption” (3.44b) ⟩
    ¬ (p ≡ q) ∨ (¬ ¬ q ∨ r) ∨ ¬ p
  = ⟨ “Commutativity of ¬ with ≡” ⟩
    (p ≡ ¬ q) ∨ (¬ ¬ q ∨ r) ∨ ¬ p
  = ⟨ “Double negation” ⟩
    (p ≡ ¬ q) ∨ q ∨ r ∨ ¬ p
  = ⟨ “Distributivity of ∨ over ≡” ⟩
    (p ∨ q ≡ ¬ q ∨ q) ∨ r ∨ ¬ p
  = ⟨ “LEM” ⟩
    (p ∨ q ≡ true) ∨ r ∨ ¬ p
  = ⟨ “Identity of ≡” ⟩
    p ∨ q  ∨ r ∨ ¬ p
  = ⟨ “LEM” ⟩
    true ∨ q  ∨ r
  = ⟨ “Zero of ∨” ⟩
    true 
 
Theorem (3.82) (3.82c) “Transitivity of ⇒”: (p ⇒ q) ∧ (q ≡ r) ⇒ (p ⇒ r)
Proof:
    (p ⇒ q) ∧ (q ≡ r) ⇒ (p ⇒ r)
  =⟨ “Definition of ⇒” (3.59)⟩
    ¬ ((p ⇒ q) ∧ (q ≡ r)) ∨ (p ⇒ r)
  =⟨ “De Morgan”⟩
    ¬ (p ⇒ q) ∨ ¬ (q ≡ r) ∨ (p ⇒ r)
  =⟨ “Definition of ⇒”⟩
    ¬ (¬ p ∨ q) ∨ ¬ (q ≡ r) ∨ (¬ p ∨ r)
  =⟨ “De Morgan”⟩
    (¬ ¬ p ∧ ¬ q) ∨ (¬ p ∨ r) ∨ ¬ (q ≡ r) 
  =⟨ “Absorption” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ ¬ (q ≡ r) 
  =⟨ “Commutativity of ¬ with ≡” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ (q ≡ ¬ r)
  =⟨ “Distributivity of ∨ over ≡” ⟩
    ¬ p ∨ ¬ q ∨ (r ∨ q ≡ r ∨ ¬ r)
  =⟨ “LEM” ⟩
    ¬ p ∨ ¬ q ∨ (r ∨ q ≡ true)
  =⟨ “Identity of ≡” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ q 
  =⟨ “LEM” ⟩
    ¬ p ∨ r ∨ true
  =⟨ “Zero of ∨” ⟩
    true  

    Theorem “Multiplying the successor”: m · (suc n) = m + m · n
Proof:
  By induction on `m : ℕ`:
    Base case `0 · (suc n) = 0 + 0 · n`:
        0 · suc n
      =⟨ “Definition of · for 0” ⟩
        0
      =⟨ “Left-identity of +” ⟩
        0 + 0
      =⟨ “Definition of · for 0” ⟩
        0 + 0 · n
    Induction step `(suc m) · (suc n) = (suc m) + (suc m) · n`:
        (suc m) · (suc n)
      =⟨ “Definition of · for `suc`”⟩
        suc n + m · (suc n)
      =⟨ Induction hypothesis⟩
        suc n + (m + m · n)
      =⟨ “Associativity of +”⟩
        (suc n + m) + m · n
      =⟨ “Definition of + for `suc`”⟩
        suc(n + m) + m · n
      =⟨ “Symmetry of +”⟩
        suc(m + n) + m · n
      =⟨ “Definition of + for `suc`”⟩
        suc(m + n + m · n)
      =⟨ “Associativity of +”⟩
        suc(m + (n + m · n))
      =⟨ “Definition of · for `suc`”⟩
        suc(m + suc m · n)
      =⟨ “Definition of + for `suc`”⟩
        suc m + suc m · n

Theorem “Symmetry of ·”: m · n = n · m
Proof:
  By induction on `m : ℕ`:
    Base case `0 · n = n · 0`:
        0 · n
      =⟨ “Definition of · for 0” ⟩
        0
      =⟨ “Right-zero of ·” ⟩
        n · 0
    Induction step `(suc m) · n = n · (suc m)` :
        suc m · n
      = ⟨ “Definition of · for `suc`” ⟩
        n + m · n
      = ⟨ Induction hypothesis ⟩ 
        n + n · m
      = ⟨ “Multiplying the successor” ⟩ 
        n · suc m
 
        
Theorem “Distributivity of · over +”: (k + m) · n = k · n + m · n
Proof:
  By induction on `k : ℕ`:
    Base case `(0 + m) · n = 0 · n + m · n`:
        (0 + m) · n
      =⟨ “Left-identity of +” ⟩
        m · n
      =⟨ “Left-identity of +” ⟩
        0 + m · n
      =⟨ “Definition of · for 0” ⟩
        0 · n + m · n
    Induction step `(suc k + m) · n = suc k · n + m · n`:
        (suc k + m) · n
      = ⟨ “Definition of + for `suc`” ⟩
         suc (k + m) · n
      = ⟨ “Definition of · for `suc`” ⟩
         n + (k + m) · n
      = ⟨ Induction hypothesis ⟩
         n + (k · n + m · n)
      = ⟨ “Associativity of +” ⟩
         (n + k · n) + m · n
      = ⟨ “Definition of · for `suc`” ⟩
         (suc k · n) + m · n

Theorem “Associativity of ·”: (k · m) · n = k · (m · n)
Proof:
  By induction on `k : ℕ`:
    Base case `(0 · m) · n = 0 · (m · n)`:
        (0 · m) · n
      = ⟨ “Definition of · for 0” ⟩
        0 · n 
      = ⟨ “Definition of · for 0” ⟩
        0 
      = ⟨ “Definition of · for 0” ⟩
        0 · (m · n)
    Induction step `(suc k · m) · n = suc k · (m · n)`:
        (suc k · m) · n
      = ⟨ “Definition of · for `suc`” ⟩
        (m + k · m) · n
      = ⟨ “Distributivity of · over +” ⟩
        m · n + (k · m) · n
      = ⟨ Induction hypothesis ⟩
        m · n + k · (m · n)
      = ⟨ “Definition of · for `suc`” ⟩
        suc k · (m · n)
        
    Theorem “Monus exchange”: m + (n - m) = n + (m - n)
Proof:
  By induction on `m : ℕ`:
    Base case `0 + (n - 0) = n + (0 - n)`:
        0 + (n - 0) = n + (0 - n)
      =⟨ “Right-identity of subtraction”⟩
        0 + n = n + (0 - n)
      =⟨ “Subtraction from zero”⟩
        0 + n = n + 0 — This is “Symmetry of +”
    Induction step `suc m + (n - suc m) = n + (suc m - n)`:
      By induction on `n : ℕ`:
        Base case `suc m + (0 - suc m) = 0 + (suc m - 0)`:
            suc m + (0 - suc m) = 0 + (suc m - 0)
          =⟨ “Right-identity of subtraction”⟩ 
            suc m + (0 - suc m) = 0 + suc m 
          =⟨ “Subtraction from zero” ⟩ 
            suc m + 0 = 0 + suc m — This is “Symmetry of +”
        Induction step `suc m + (suc n - suc m) = suc n + (suc m - suc n)`:
            suc m + (suc n - suc m)
          = ⟨ “Subtraction of successor from successor” ⟩ 
            suc m + (n - m)
          = ⟨ “Definition of + for `suc`”  ⟩ 
            suc (m + (n - m))
          = ⟨ Induction hypothesis `m + (n - m) = n + (m - n)` ⟩ 
            suc (n + (m - n))
          = ⟨ “Definition of + for `suc`” ⟩ 
            suc n + (m - n)
          = ⟨ “Subtraction of successor from successor” ⟩ 
            suc n + (suc m - suc n)
             Theorem (3.89) “Shannon”: E[z ≔ p] ≡ (p ∧ E[z ≔ true]) ∨ (¬ p ∧ E[z ≔ false])
Proof:
    E[z ≔ p]
  =⟨ “Identity of ∧”⟩
    true ∧ E[z ≔ p] 
  =⟨ “LEM”⟩
    (p ∨ ¬ p) ∧ E[z ≔ p] 
  =⟨ “Distributivity of ∧ over ∨”⟩
    (p ∧ E[z ≔ p]) ∨ (¬ p ∧ E[z ≔ p])
  =⟨ “Replace by `true`” (3.87)⟩
    (p ∧ E[z ≔ true]) ∨ (¬ p ∧ E[z ≔ p])
  =⟨ “Definition of ¬ from ≡”⟩
    (p ∧ E[z ≔ true]) ∨ ((p ≡ false) ∧ E[z ≔ p])
  =⟨ “Replacement” (3.84a) with “Definition of ≡”⟩
    (p ∧ E[z ≔ true]) ∨ ((p ≡ false) ∧ E[z ≔ false])
  =⟨ “Definition of ¬ from ≡” ⟩
    (p ∧ E[z ≔ true]) ∨ (¬ p ∧ E[z ≔ false])

    Calculation:
    (5 + u) - 8
  ≤⟨ “≤-Antitonicity of -” with Fact `7 ≤ 8` ⟩
    (5 + u) - 7
  =⟨ “Mutual associativity of + and -” ⟩
    5 + (u - 7)
  ≤⟨ “≤-Monotonicity of +” with Fact `5 ≤ 6` ⟩
    6 + (u - 7)
  =⟨ “Symmetry of +” ⟩
    (u - 7) + 6
  ≤⟨ “≤-Monotonicity of +” with 
      “≤-Antitonicity of -” with Fact `4 ≤ 7` ⟩
    (u - 4) + 6
  =⟨ “Symmetry of +” ⟩
    6 + (u - 4)
  =⟨ “Mutual associativity of + and -” ⟩
    6 + u - 4
  ≤⟨ “≤-Monotonicity of -” with
     “≤-Monotonicity of +” with Fact `6 ≤ 7` ⟩
    (7 + u) - 4
  ≤⟨ “≤-Antitonicity of -” with Fact `3 ≤ 4` ⟩
    (7 + u) - 3

    Theorem (4.2) “Left-monotonicity of ∨” “Monotonicity of ∨”:
    (p ⇒ q) ⇒ (p ∨ r) ⇒ (q ∨ r)
Proof:
  Assuming `p ⇒ q`, `p ∨ r`:
    By cases: `p`, `r`
      Completeness: By Assumption `p ∨ r`
      Case `p`:
          true
        =⟨ Assumption `p`⟩ 
          p
        ⇒⟨ Assumption `p ⇒ q` ⟩
          q
        ⇒⟨ “Strengthening” (3.76a) ⟩ 
          q ∨ r
      Case `r`:
          true
        =⟨ Assumption `r`⟩ 
          r
        ⇒⟨ “Strengthening” (3.76a) ⟩
          q ∨ r


Theorem (4.2) “Left-monotonicity of ∨” “Monotonicity of ∨”:
    (p ⇒ q) ⇒ (p ∨ r) ⇒ (q ∨ r)
Proof:
  Assuming `p ⇒ q`, `p ∨ r`:
    By cases: `p`, `r`
      Completeness: By Assumption `p ∨ r`
      Case `p`:
          q ∨ r
        ⇐⟨ “Strengthening” (3.76a) ⟩
          q
        ⇐⟨ Assumption `p ⇒ q` ⟩ 
          p
        =⟨ Assumption `p`⟩
          true 
      Case `r`:
          q ∨ r
        ⇐⟨ “Strengthening” (3.76a) ⟩
          r
        =⟨ Assumption `r`⟩
          true

Theorem (4.3) “Left-monotonicity of ∧” “Monotonicity of ∧”:
    (p ⇒ q) ⇒ ((p ∧ r) ⇒ (q ∧ r))
Proof:
      (p ⇒ q) ⇒ ((p ∧ r) ⇒ (q ∧ r))
    ≡⟨ “Definition of ⇒” (3.60) ⟩
      (p ∧ q ≡ p) ⇒ ((p ∧ r) ⇒ (q ∧ r))
  Proof for this:
    Assuming `p ∧ q ≡ p`:
        p ∧ r
      =⟨ Assumption `p ∧ q ≡ p` ⟩ 
        p ∧ q ∧ r
      ⇒⟨ “Weakening” (3.76b) ⟩
        q ∧ r
Theorem (15.35) “Positivity under positive ·”: pos a ⇒ (pos b ≡ pos (a · b))
Proof:
  Assuming `pos a`:
      pos b ≡ pos (a · b)
    =⟨ “Mutual implication” ⟩
      (pos b ⇒ pos (a · b)) ∧ (pos (a · b) ⇒ pos b)
    =⟨ “Identity of ∧” , Assumption `pos a` ⟩
      (pos b ∧ pos a ⇒ pos (a · b)) ∧ (pos (a · b) ⇒ pos b)
    =⟨ “Positivity under ·” , “Identity of ∧”⟩
      pos (a · b) ⇒ pos b
    =⟨ “Subproof” with Assumption `pos a` ⟩ 
      true

      Theorem “Antitonicity of ⇒” “Left-antitonicity of ⇒”:
    (p ⇒ q) ⇒ ((q ⇒ r) ⇒ (p ⇒ r))
Proof:
    (p ⇒ q)
  ⇒⟨ “Strengthening” (3.76a) ⟩
    (p ⇒ q) ∨ r
  =⟨ “Contrapositive”  ⟩
    (¬ q ⇒ ¬ p) ∨ r
  =⟨ “Distributivity of ∨ over ⇒” ⟩
    (¬ q ∨ r) ⇒ (¬ p ∨ r)
  =⟨ “Material implication” ⟩
    (q ⇒ r) ⇒ (p ⇒ r)

Theorem “Left-monotonicity of ∨” “Monotonicity of ∨”:
    (p ⇒ q) ⇒ (p ∨ r) ⇒ (q ∨ r)
Proof:
  Assuming `p ⇒ q`:
      p ∨ r
    ⇒⟨ “Strengthening” (3.76a) ⟩ 
      (p ∨ q) ∨ r
    =⟨ Assumption `p ⇒ q` with “Definition of ⇒” (3.57) ⟩ 
      q ∨ r

      Lemma “Cancellation of multiplication with successor”:
    suc c · a = suc c · b  ≡  a = b
Proof:
  By induction on `a : ℕ`:
    Base case `suc c · 0 = suc c · b  ≡  0 = b`:
        suc c · 0 = suc c · b
      ≡⟨ “Right-zero of ·” ⟩
        0 = suc c · b
      ≡⟨ “Definition of · for `suc`” ⟩
        0 = b + c · b
      ≡⟨ “Zero sum” ⟩
        0 = b ∧ 0 = c · b
      ≡⟨ Substitution ⟩
        0 = b ∧ (0 = c · z)[z ≔ b]
      ≡⟨ “Replacement” ⟩
        0 = b ∧ (0 = c · z)[z ≔ 0]
      ≡⟨ Substitution ⟩
        0 = b ∧ 0 = c · 0
      ≡⟨ “Right-zero of ·” ⟩
        0 = b ∧ true
      ≡⟨ “Identity of ∧” ⟩
        0 = b
    Induction step `suc c · suc a = suc c · b  ≡  suc a = b`:
      By induction on `b : ℕ`:
        Base case `suc c · suc a = suc c · 0  ≡  suc a = 0`:
            suc c · suc a = suc c · 0
          ≡⟨ “Right-zero of ·” ⟩
            suc c · suc a = 0
          ≡⟨ “Zero is not product of successors” ⟩
            false
          ≡⟨ “Zero is not successor” ⟩
            suc a = 0
        Induction step `suc c · suc a = suc c · suc b  ≡  suc a = suc b`:
            suc c · suc a = suc c · suc b
          ≡⟨ “Multiplying the successor” ⟩
            suc c + suc c · a = suc c + suc c · b
          ≡⟨ “Cancellation of +” ⟩
            suc c · a = suc c · b
          ≡⟨ Induction hypothesis `suc c · a = suc c · b  ≡  a = b` ⟩
            a = b
          ≡⟨ “Cancellation of `suc`” ⟩
            suc a = suc b
      
Theorem “Cancellation of ·”:
    c ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
Proof:
  By cases: `c = 0`, `c = suc (pred c)`
    Completeness: By “Zero or successor of predecessor”
    Case `c = 0`:
        c ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
      =⟨ Assumption `c = 0`⟩
        0 ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
      =⟨ “Irreflexivity of ≠” ⟩
        false ⇒ (c · a = c · b  ≡  a = b)
      =⟨ “ex falso quodlibet” ⟩
        true
    Case `c = suc (pred c)`:
         c ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
      =⟨ Assumption `c = suc (pred c)`⟩
         suc (pred c) ≠ 0 ⇒ (suc (pred c) · a = suc (pred c) · b  ≡  a = b)
      =⟨ “Zero is not successor” ⟩
         true ⇒ (suc (pred c) · a = suc (pred c) · b  ≡  a = b)
      =⟨ “Cancellation of multiplication with successor” ⟩
         true ⇒ true
      =⟨ “Reflexivity of ⇒” ⟩
         true    

         Theorem “Zero or successor of predecessor”: n = 0 ∨ n = suc (pred n)
Proof:
    n ≠ 0 ≡ n = suc (pred n)    — This is “Predecessor of non-zero”
  =⟨ “Definition of ≠” ⟩
    ¬ (n = 0) ≡ n = suc (pred n)
  =⟨ “Mutual implication” ⟩
    (¬ (n = 0) ⇒ n = suc (pred n)) ∧ (n = suc (pred n) ⇒ ¬ (n = 0))
  ⇒⟨ “Strengthening” (3.76b) ⟩
    ¬ (n = 0) ⇒ n = suc (pred n)
  =⟨ “Material implication” ⟩
    ¬ ¬ (n = 0) ∨ n = suc (pred n)
  =⟨ “Double negation” ⟩
    n = 0 ∨ n = suc (pred n)
 
Theorem “Right-identity of subtraction”: m - 0 = m
Proof:
  By cases: `m = 0`, `m = suc (pred m)`
    Completeness: By “Zero or successor of predecessor”
    Case `m = 0`:
        m - 0 = m
      ≡⟨ Assumption `m = 0` ⟩
        0 - 0 = 0
      — This is “Subtraction from zero”
    Case `m = suc (pred m)`:
        m - 0
      =⟨ Assumption `m = suc (pred m)` ⟩
        (suc (pred m)) - 0
      =⟨ “Subtraction of zero from successor” ⟩
        suc (pred m)
      =⟨ Assumption `m = suc (pred m)` ⟩
        m
