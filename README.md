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
