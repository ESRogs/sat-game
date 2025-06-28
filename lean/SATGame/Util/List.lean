import Batteries.Data.List.Basic

/-!
# List Utilities

Helper theorems for proving termination via list sum properties.

This file contains general-purpose theorems about lists that could be useful
in various contexts, not specific to SAT or Boolean logic.
-/

-- Helper: filterMap sum is at most original sum when elements don't increase
theorem List.filterMap_sum_le {α β : Type} (l : List α) (g : α → Option β) (h : β → Nat) (f : α → Nat)
    (h_nonincreasing : ∀ a ∈ l, ∀ b, g a = some b → h b ≤ f a) :
    ((l.filterMap g).map h).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases h_g : g head with
    | none =>
      simp only [h_g]
      have h_tail : ∀ a ∈ tail, ∀ b, g a = some b → h b ≤ f a := by
        intros a ha b hb
        exact h_nonincreasing a (List.mem_cons_of_mem head ha) b hb
      show ((tail.filterMap g).map h).sum ≤ f head + (tail.map f).sum
      exact Nat.le_trans (ih h_tail) (Nat.le_add_left (tail.map f).sum (f head))
    | some head_result =>
      simp only [h_g, List.map_cons, List.sum_cons]
      have h_head_le : h head_result ≤ f head := by
        have h_mem : head ∈ head :: tail := List.mem_cons_self
        exact h_nonincreasing head h_mem head_result h_g
      have h_tail : ∀ a ∈ tail, ∀ b, g a = some b → h b ≤ f a := by
        intros a ha b hb
        exact h_nonincreasing a (List.mem_cons_of_mem head ha) b hb
      exact Nat.add_le_add h_head_le (ih h_tail)

-- Specific utility for setVariable proof: witness element removed
theorem List.sum_filterMap_lt_of_witness_removed {α β : Type}
    (l : List α) (f : α → Nat) (g : α → Option β) (h : β → Nat)
    (witness : α) (h_witness_mem : witness ∈ l)
    (h_witness_removed : g witness = none)
    (h_witness_pos : f witness > 0)
    (h_others_nonincreasing : ∀ a ∈ l, ∀ b, g a = some b → h b ≤ f a) :
    ((l.filterMap g).map h).sum < (l.map f).sum := by
  -- Use induction on the list
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h_eq : head = witness
    · -- Case: head is the witness
      subst h_eq
      rw [h_witness_removed]
      simp only [List.map_nil, List.sum_nil, Nat.zero_add]
      -- Now we need: ((tail.filterMap g).map h).sum < f head + (tail.map f).sum
      have h_tail_le : ((tail.filterMap g).map h).sum ≤ (tail.map f).sum := by
        apply filterMap_sum_le
        intros a ha b hb
        -- After subst, need to reason about membership in the original list
        have h_mem_orig : a ∈ head :: tail := List.mem_cons_of_mem head ha
        exact h_others_nonincreasing a h_mem_orig b hb
      calc ((tail.filterMap g).map h).sum
        ≤ (tail.map f).sum := h_tail_le
        _ < f head + (tail.map f).sum := Nat.lt_add_of_pos_left h_witness_pos
    · -- Case: head is not the witness
      have h_witness_in_tail : witness ∈ tail := by
        rw [List.mem_cons] at h_witness_mem
        cases h_witness_mem with
        | inl h => exact absurd h.symm h_eq
        | inr h => exact h
      -- Apply IH to tail
      have h_tail_others : ∀ a ∈ tail, ∀ b, g a = some b → h b ≤ f a := by
        intros a ha b hb
        exact h_others_nonincreasing a (List.mem_cons_of_mem head ha) b hb
      have ih_result := ih h_witness_in_tail h_tail_others
      cases h_g : g head with
      | none =>
        -- Head gets filtered out
        simp only [h_g]
        show ((tail.filterMap g).map h).sum < f head + (tail.map f).sum
        calc ((tail.filterMap g).map h).sum
          < (tail.map f).sum := ih_result
          _ ≤ f head + (tail.map f).sum := Nat.le_add_left (tail.map f).sum (f head)
      | some head_result =>
        -- Head passes through
        simp only [h_g, List.map_cons, List.sum_cons]
        have h_head_le : h head_result ≤ f head := by
          exact h_others_nonincreasing head (List.mem_cons_self) head_result h_g
        show h head_result + ((tail.filterMap g).map h).sum < f head + (tail.map f).sum
        calc h head_result + ((tail.filterMap g).map h).sum
          < h head_result + (tail.map f).sum := Nat.add_lt_add_left ih_result _
          _ ≤ f head + (tail.map f).sum := Nat.add_le_add_right h_head_le _

-- Specific utility for setVariable proof: witness element decreased
theorem List.sum_filterMap_lt_of_witness_decreased {α β : Type}
    (l : List α) (f : α → Nat) (g : α → Option β) (h : β → Nat)
    (witness : α) (h_witness_mem : witness ∈ l)
    (witness_result : β) (h_witness_maps : g witness = some witness_result)
    (h_witness_decreased : h witness_result < f witness)
    (h_others_nonincreasing : ∀ a ∈ l, ∀ b, g a = some b → h b ≤ f a) :
    ((l.filterMap g).map h).sum < (l.map f).sum := by
  -- Use induction on the list
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h_eq : head = witness
    · -- Case: head is the witness
      subst h_eq
      rw [h_witness_maps]
      simp only [List.map_cons, List.sum_cons]
      -- Now we need: h witness_result + ((tail.filterMap g).map h).sum < f head + (tail.map f).sum
      have h_tail_le : ((tail.filterMap g).map h).sum ≤ (tail.map f).sum := by
        apply filterMap_sum_le
        intros a ha b hb
        exact h_others_nonincreasing a (List.mem_cons_of_mem head ha) b hb
      calc h witness_result + ((tail.filterMap g).map h).sum
        ≤ h witness_result + (tail.map f).sum := Nat.add_le_add_left h_tail_le _
        _ < f head + (tail.map f).sum := Nat.add_lt_add_right h_witness_decreased (tail.map f).sum
    · -- Case: head is not the witness
      have h_witness_in_tail : witness ∈ tail := by
        rw [List.mem_cons] at h_witness_mem
        cases h_witness_mem with
        | inl h => exact absurd h.symm h_eq
        | inr h => exact h
      -- Apply IH to tail
      have h_tail_others : ∀ a ∈ tail, ∀ b, g a = some b → h b ≤ f a := by
        intros a ha b hb
        exact h_others_nonincreasing a (List.mem_cons_of_mem head ha) b hb
      have ih_result := ih h_witness_in_tail h_tail_others
      cases h_g : g head with
      | none =>
        -- Head gets filtered out
        simp only [h_g]
        show ((tail.filterMap g).map h).sum < f head + (tail.map f).sum
        calc ((tail.filterMap g).map h).sum
          < (tail.map f).sum := ih_result
          _ ≤ f head + (tail.map f).sum := Nat.le_add_left (tail.map f).sum (f head)
      | some head_result =>
        -- Head passes through
        simp only [h_g, List.map_cons, List.sum_cons]
        have h_head_le : h head_result ≤ f head := by
          exact h_others_nonincreasing head (List.mem_cons_self) head_result h_g
        show h head_result + ((tail.filterMap g).map h).sum < f head + (tail.map f).sum
        calc h head_result + ((tail.filterMap g).map h).sum
          < h head_result + (tail.map f).sum := Nat.add_lt_add_left ih_result _
          _ ≤ f head + (tail.map f).sum := Nat.add_le_add_right h_head_le _

-- General lemma: erasing any element never increases the sum
theorem List.sum_map_eraseIdx_le {α : Type} (l : List α) (f : α → Nat) (index : Nat) :
    ((l.eraseIdx index).map f).sum ≤ (l.map f).sum := by
  by_cases h_index : index < l.length
  · -- Valid index: eraseIdx creates a sublist, and sum over sublist ≤ original sum
    -- Use induction on the list structure
    induction l generalizing index with
    | nil =>
      simp at h_index  -- contradiction: index < 0
    | cons head tail ih =>
      cases index with
      | zero =>
        -- Removing head: eraseIdx 0 (head :: tail) = tail
        simp only [List.eraseIdx_cons_zero, List.map_cons, List.sum_cons]
        exact Nat.le_add_left (tail.map f).sum (f head)
      | succ n =>
        -- Removing from tail: eraseIdx (n+1) (head :: tail) = head :: eraseIdx n tail
        simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons]
        -- Apply inductive hypothesis to tail
        have h_tail_index : n < tail.length := by
          -- From h_index : n.succ < (head :: tail).length = tail.length.succ
          simp only [List.length_cons] at h_index
          exact Nat.lt_of_succ_lt_succ h_index
        have ih_applied := ih n h_tail_index
        -- Goal: f head + ((tail.eraseIdx n).map f).sum ≤ f head + (tail.map f).sum
        exact Nat.add_le_add_left ih_applied (f head)
  · -- Invalid index: no change
    simp [List.eraseIdx_of_length_le (Nat.le_of_not_gt h_index)]

-- If a list contains an element > 0, then the sum > 0
theorem List.sum_pos (l : List Nat) (h : ∃ x ∈ l, x > 0) : l.sum > 0 := by
  -- Use list induction on the structure
  induction l with
  | nil => 
    -- Impossible case: x cannot be in empty list
    let ⟨x, h_mem, h_pos⟩ := h
    simp at h_mem
  | cons head tail ih =>
    -- Extract the witness: there exists an element x in head::tail with x > 0
    let ⟨x, h_mem, h_pos⟩ := h
    -- Case analysis: is x the head or in the tail?
    by_cases h_eq : head = x
    · -- Case: head is our positive element
      subst h_eq
      -- Sum = head + tail.sum = x + tail.sum > 0 since x > 0
      simp [List.sum_cons]
      exact Nat.add_pos_left h_pos tail.sum
    · -- Case: x is in the tail
      have h_mem_tail : x ∈ tail := by
        rw [List.mem_cons] at h_mem
        cases h_mem with
        | inl h => exact absurd h.symm h_eq
        | inr h => exact h
      -- Apply induction hypothesis: tail.sum > 0
      have ih_applied : tail.sum > 0 := ih ⟨x, h_mem_tail, h_pos⟩
      -- Therefore head + tail.sum > head + 0 = head ≥ 0, so total > 0
      simp [List.sum_cons]
      exact Nat.add_pos_right head ih_applied

-- If a list contains an element ≥ 1, then the sum > 0
theorem List.sum_pos_of_mem_ge_one (l : List Nat) (h : ∃ x ∈ l, x ≥ 1) : l.sum > 0 := by
  -- Convert ≥ 1 to > 0 and apply the previous theorem
  let ⟨x, h_mem, h_ge_one⟩ := h
  have h_pos : x > 0 := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp h_ge_one))
  exact List.sum_pos l ⟨x, h_mem, h_pos⟩

-- Removing an element with positive contribution decreases the sum
theorem sum_eraseIdx_lt {α : Type} (l : List α) (f : α → Nat) (index : Nat)
    (h_index : index < l.length)
    (h_pos : f (l.get ⟨index, h_index⟩) > 0) :
    ((l.eraseIdx index).map f).sum < (l.map f).sum := by
  -- Use induction on the index with the structural theorems
  induction index generalizing l with
  | zero =>
    -- Base case: index = 0, so we're removing the head
    cases l with
    | nil =>
      simp at h_index  -- contradiction: 0 < 0
    | cons head tail =>
      simp [List.eraseIdx_cons_zero, List.map, List.sum]
      -- Goal: tail.map f).sum < f head + (tail.map f).sum
      -- This follows from h_pos: f head > 0
      exact Nat.lt_add_of_pos_left h_pos
  | succ n ih =>
    -- Inductive case: index = n + 1
    cases l with
    | nil =>
      simp at h_index  -- contradiction: n + 1 < 0
    | cons head tail =>
      simp [List.eraseIdx_cons_succ, List.map, List.sum]
      -- Goal: f head + (tail.eraseIdx n).map f).sum < f head + (tail.map f).sum
      -- Use the inductive hypothesis on the tail
      have ih_applied := ih tail
      have h_tail_index : n < tail.length := by
        simp [List.length] at h_index ⊢
        omega
      have h_tail_pos : f (tail.get ⟨n, h_tail_index⟩) > 0 := by
        simp [List.get] at h_pos ⊢
        exact h_pos
      have tail_sum_lt := ih_applied h_tail_index h_tail_pos
      -- Show that this is exactly what we need
      show (List.map f (tail.eraseIdx n)).sum < (List.map f tail).sum
      exact tail_sum_lt
