import SATGame.CNF.Satisfiability
import SATGame.FormulaOps.FormulaExt
import SATGame.FormulaOps.FormulaOps
import SATGame.FormulaOps.ValidSequences
import SATGame.FormulaOps.Termination.Nonterminal

/-!
# Formula Operation Preservation Properties ✅ COMPLETE

This module proves mathematical preservation properties for formula operations.
These theorems establish that certain logical properties are preserved under formula transformations.

## Single Operation Preservation
1. `setVariable_preserves_unsatisfiability`: Variable assignment preserves unsatisfiability
2. `removeClause_preserves_satisfiability`: Clause removal preserves satisfiability

## Sequence Operation Preservation
3. `valid_variable_assignment_sequence_preserves_unsatisfiability`: Valid variable assignment sequences preserve unsatisfiability
4. `valid_clause_removal_sequence_preserves_satisfiability`: Valid clause removal sequences preserve satisfiability

## Mathematical Significance

These preservation properties are fundamental to understanding how formula operations affect satisfiability:
- Variable assignment can transform satisfiable formulas but cannot create satisfiability from unsatisfiable formulas
- Clause removal can transform unsatisfiable formulas but cannot destroy satisfiability from satisfiable formulas
- Valid operation sequences maintain these preservation properties throughout the transformation process
-/

/-- Helper: If a clause is satisfied by variable assignment, the extended assignment satisfies it -/
theorem satisfied_clause_remains_satisfied {Var : Type} [DecidableEq Var]
    (clause : Clause Var) (var : Var) (value : Bool) (α : Assignment Var) :
    clause.satisfiedBy var value = true →
    clause.satisfiedByAssignment (fun v => if v = var then value else α v) = true := by
  intro h_satisfied
  unfold Clause.satisfiedByAssignment
  rw [List.any_eq_true]
  -- Extract the literal that made the clause satisfied
  unfold Clause.satisfiedBy at h_satisfied
  rw [List.any_eq_true] at h_satisfied
  obtain ⟨lit, h_lit_in_clause, h_lit_becomes_true⟩ := h_satisfied
  exists lit
  constructor
  · exact h_lit_in_clause
  · exact becomesTrueUnder_implies_satisfiedBy_extension lit var value α h_lit_becomes_true

/-- Helper: If a clause survives setVariable, any assignment satisfying the result can be extended -/
theorem filtered_clause_satisfaction_extends {Var : Type} [DecidableEq Var]
    (orig_clause filtered_clause : Clause Var) (var : Var) (value : Bool) (α : Assignment Var) :
    processClauseForVariableAssignment orig_clause var value = some filtered_clause →
    filtered_clause.satisfiedByAssignment α = true →
    orig_clause.satisfiedByAssignment (fun v => if v = var then value else α v) = true := by
  intro h_process h_filtered_sat
  unfold Clause.satisfiedByAssignment at h_filtered_sat ⊢
  rw [List.any_eq_true] at h_filtered_sat ⊢
  obtain ⟨lit, h_lit_in_filtered, h_lit_sat⟩ := h_filtered_sat

  -- This literal was in the original clause (since filtering only removes)
  have h_lit_in_orig : List.Mem lit orig_clause := by
    -- We know h_process : processClauseForVariableAssignment orig_clause var value = some filtered_clause
    -- and h_lit_in_filtered : lit ∈ filtered_clause
    unfold processClauseForVariableAssignment at h_process
    split at h_process
    · -- Case: orig_clause.satisfiedBy var value = true
      simp at h_process
    · -- Case: orig_clause.satisfiedBy var value = false
      -- h_process : some (orig_clause.filter ...) = some filtered_clause
      simp at h_process
      -- So filtered_clause = orig_clause.filter ...
      rw [← h_process] at h_lit_in_filtered
      -- lit ∈ orig_clause.filter ... means lit ∈ orig_clause
      exact List.mem_filter.mp h_lit_in_filtered |>.1

  exists lit
  constructor
  · exact h_lit_in_orig
  · -- The literal doesn't contain var (since it survived filtering), so assignment extension preserves satisfaction
    have h_lit_no_var : ¬(lit.containsVariable var) := by
      -- The literal survived filtering, so it doesn't contain var
      unfold processClauseForVariableAssignment at h_process
      split at h_process
      · -- Case: orig_clause.satisfiedBy var value = true
        simp at h_process
      · -- Case: orig_clause.satisfiedBy var value = false
        simp at h_process
        -- filtered_clause = orig_clause.filter (fun lit => ¬(lit.containsVariable var))
        rw [← h_process] at h_lit_in_filtered
        -- Extract the filter condition
        have h_mem := List.mem_filter.mp h_lit_in_filtered
        -- The second component gives us the filter condition
        -- h_mem.2 : (!lit.containsVariable var) = true
        have h_bool : (!lit.containsVariable var) = true := h_mem.2
        -- If !b = true, then b = false
        have h_false : lit.containsVariable var = false := by
          cases h_eq : lit.containsVariable var with
          | true =>
            rw [h_eq] at h_bool
            simp at h_bool
          | false => rfl
        -- Convert b = false to ¬b
        simp [h_false]
    rw [← assignment_extension_preserves_unrelated_literals lit α var value h_lit_no_var]
    exact h_lit_sat

/--
**Variable Assignment Preservation**: Variable assignment preserves unsatisfiability.

Setting a variable in an unsatisfiable formula keeps it unsatisfiable.
This requires careful analysis of how variable assignment works on unsatisfiable formulas.
-/
theorem setVariable_preserves_unsatisfiability {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (var : Var) (value : Bool)
    (h_unsat : ¬formula.IsSatisfiable) :
    ¬(formula.setVariable var value).IsSatisfiable := by
  -- Prove by contrapositive: if setVariable result is satisfiable, then original is satisfiable
  intro h_result_sat
  obtain ⟨α, h_α_satisfies_result⟩ := h_result_sat

  -- Extend α to satisfy the original formula
  let extended_α : Assignment Var := fun v => if v = var then value else α v

  -- Show this extended assignment satisfies the original formula
  have h_extended_satisfies_original : formula.satisfiedByAssignment extended_α = true := by
    unfold Formula.satisfiedByAssignment
    rw [List.all_eq_true]
    intro clause h_clause_in_formula

    -- Case analysis: was this clause satisfied by the variable assignment?
    by_cases h_satisfied : clause.satisfiedBy var value = true
    · -- Case 1: Clause was satisfied and removed
      exact satisfied_clause_remains_satisfied clause var value α h_satisfied
    · -- Case 2: Clause was filtered and appears in result
      -- Find the corresponding filtered clause in the result
      have h_filtered_exists : ∃ filtered_clause,
          processClauseForVariableAssignment clause var value = some filtered_clause ∧
          List.Mem filtered_clause (formula.setVariable var value) := by
        unfold Formula.setVariable
        exists clause.filter (fun lit => ¬(lit.containsVariable var))
        constructor
        · -- Show processClauseForVariableAssignment clause var value = some filtered_clause
          unfold processClauseForVariableAssignment
          rw [if_neg h_satisfied]
        · -- Show filtered_clause ∈ formula.setVariable var value
          -- formula.setVariable = formula.filterMap (processClauseForVariableAssignment · var value)
          -- We need to show clause.filter ... ∈ formula.filterMap ...
          apply List.mem_filterMap.mpr
          exists clause
          constructor
          · exact h_clause_in_formula
          · -- processClauseForVariableAssignment clause var value = some (clause.filter ...)
            unfold processClauseForVariableAssignment
            rw [if_neg h_satisfied]

      obtain ⟨filtered_clause, h_process, h_in_result⟩ := h_filtered_exists

      -- α satisfies this filtered clause
      unfold Formula.satisfiedByAssignment at h_α_satisfies_result
      rw [List.all_eq_true] at h_α_satisfies_result
      have h_filtered_sat := h_α_satisfies_result filtered_clause h_in_result

      -- Extended assignment satisfies original clause
      exact filtered_clause_satisfaction_extends clause filtered_clause var value α h_process h_filtered_sat

  -- This contradicts the assumption that the original formula is unsatisfiable
  exact h_unsat ⟨extended_α, h_extended_satisfies_original⟩

/-- A valid sequence of variable assignments preserves unsatisfiability -/
theorem valid_variable_assignment_sequence_preserves_unsatisfiability {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_unsatisfiable : ¬formula.IsSatisfiable)
    {assignments : List (FormulaOp Var)}
    (valid_sequence : valid_variable_assignment_sequence formula assignments) :
    ¬(assignments.foldl Formula.applyOp formula).IsSatisfiable := by
  -- Induction on the valid sequence structure
  induction valid_sequence with
  | nil =>
    -- Empty list: formula unchanged
    simp [List.foldl_nil]
    exact h_unsatisfiable
  | cons h_nonterminal h_is_setvar h_applicable h_rest_valid ih =>
    -- List = op :: rest, where op is a valid setVariable
    simp [List.foldl_cons]
    -- Apply inductive hypothesis to (formula.applyOp op)
    apply ih
    -- The formula after op is still unsatisfiable
    obtain ⟨var, value, h_op_eq⟩ := h_is_setvar
    rw [h_op_eq]
    unfold Formula.applyOp
    simp
    exact setVariable_preserves_unsatisfiability _ var value h_unsatisfiable

/--
**Clause Removal Preservation**: Clause removal preserves satisfiability.

Removing a clause from a satisfiable formula keeps it satisfiable.
This is trivial - removing constraints can only make formulas easier to satisfy.
-/
theorem removeClause_preserves_satisfiability {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (index : Nat)
    (h_sat : formula.IsSatisfiable) :
    (formula.removeClause index).IsSatisfiable := by
  -- Extract the satisfying assignment
  obtain ⟨α, h_α_satisfies⟩ := h_sat

  -- Show the same assignment satisfies the formula with clause removed
  unfold Formula.IsSatisfiable
  exists α
  unfold Formula.satisfiedByAssignment at h_α_satisfies ⊢
  simp only [Formula.removeClause] at ⊢
  rw [List.all_eq_true] at h_α_satisfies ⊢

  -- Every clause in the erased formula was in the original formula
  intro clause h_clause_in_erased
  -- If clause is in eraseIdx, then it was in the original formula
  have h_clause_in_orig : List.Mem clause formula := List.mem_of_mem_eraseIdx h_clause_in_erased
  exact h_α_satisfies clause h_clause_in_orig

/-- A valid sequence of clause removals preserves satisfiability -/
theorem valid_clause_removal_sequence_preserves_satisfiability {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_satisfiable : formula.IsSatisfiable)
    {removals : List (FormulaOp Var)}
    (valid_sequence : valid_clause_removal_sequence formula removals) :
    (removals.foldl Formula.applyOp formula).IsSatisfiable := by
  -- Induction on the valid sequence structure
  induction valid_sequence with
  | nil =>
    -- Empty list: formula unchanged
    simp [List.foldl_nil]
    exact h_satisfiable
  | cons h_nonterminal h_is_remove h_applicable h_rest_valid ih =>
    -- List = op :: rest, where op is a valid removeClause
    simp [List.foldl_cons]
    -- Apply inductive hypothesis to (formula.applyOp op)
    apply ih
    -- The formula after op is still satisfiable
    obtain ⟨index, h_op_eq⟩ := h_is_remove
    rw [h_op_eq]
    unfold Formula.applyOp
    simp
    exact removeClause_preserves_satisfiability _ index h_satisfiable

/--
**Satisfiability Preservation Under Witness Assignment**: Setting a variable to its value
in a satisfying assignment preserves satisfiability.

This mathematical property shows that if an assignment satisfies a formula, then
partially applying that assignment (setting any variable to its assigned value)
still yields a satisfiable formula.
-/
theorem setVariable_preserves_satisfiability_under_witness {Var : Type} [DecidableEq Var]
    (formula : Formula Var) (assignment : Assignment Var) (var : Var)
    (h_satisfies : formula.satisfiedByAssignment assignment = true) :
    (formula.setVariable var (assignment var)).satisfiedByAssignment assignment = true := by
  -- We need to show that the processed formula is still satisfied by the assignment
  unfold Formula.setVariable Formula.satisfiedByAssignment

  -- Show all clauses in the filterMap result are satisfied
  rw [List.all_eq_true]
  intro processed_clause h_processed_in

  -- processed_clause came from filterMap, so there's an original clause that produced it
  rw [List.mem_filterMap] at h_processed_in
  obtain ⟨original_clause, h_orig_in, h_process_result⟩ := h_processed_in

  -- Analyze how processClauseForVariableAssignment processed this clause
  unfold processClauseForVariableAssignment at h_process_result

  -- h_process_result says processClauseForVariableAssignment returned some
  -- This means the clause was NOT satisfied by var alone
  split_ifs at h_process_result with h_satisfied
  -- Only the "not satisfied" case remains (otherwise none ≠ some)
  -- So we know h_satisfied : ¬(original_clause.satisfiedBy var (assignment var) = true)
  simp at h_process_result
  -- processed_clause = List.filter ...
  rw [← h_process_result]

  -- The original clause was satisfied by the full assignment
  have h_orig_satisfied : original_clause.satisfiedByAssignment assignment = true := by
    -- We have h_satisfies : formula.satisfiedByAssignment assignment = true
    -- and h_orig_in : original_clause ∈ formula
    unfold Formula.satisfiedByAssignment at h_satisfies
    rw [List.all_eq_true] at h_satisfies
    exact h_satisfies original_clause h_orig_in

  -- There must exist a literal in the original clause that satisfies it
  unfold Clause.satisfiedByAssignment at h_orig_satisfied ⊢
  rw [List.any_eq_true] at h_orig_satisfied ⊢
  obtain ⟨lit, h_lit_in_orig, h_lit_satisfied⟩ := h_orig_satisfied

  -- We claim this literal doesn't contain var (otherwise clause would be satisfied by var alone)
  have h_lit_no_var : ¬(lit.containsVariable var) := by
    by_contra h_lit_has_var

    -- If lit contains var, then it would be satisfied by var := assignment(var)
    have h_lit_becomes_true : lit.becomesTrueUnder var (assignment var) = true := by
      unfold Literal.becomesTrueUnder
      simp [h_lit_has_var]
      -- We need to show lit.eval (assignment var) = true
      unfold Literal.satisfiedByAssignment at h_lit_satisfied
      cases lit with
      | pos v =>
        unfold Literal.containsVariable Literal.getVariable at h_lit_has_var
        simp at h_lit_has_var
        subst h_lit_has_var
        exact h_lit_satisfied
      | neg v =>
        unfold Literal.containsVariable Literal.getVariable at h_lit_has_var
        simp at h_lit_has_var
        subst h_lit_has_var
        exact h_lit_satisfied

    -- Then the original clause would be satisfied by var alone
    have h_clause_satisfied : original_clause.satisfiedBy var (assignment var) = true := by
      unfold Clause.satisfiedBy
      rw [List.any_eq_true]
      exact ⟨lit, h_lit_in_orig, h_lit_becomes_true⟩

    -- But we know it's NOT satisfied by var alone
    contradiction

  -- Since lit doesn't contain var, it survives the filtering
  have h_lit_in_filtered : lit ∈ (List.filter (fun lit => !lit.containsVariable var) original_clause) := by
    rw [List.mem_filter]
    constructor
    · exact h_lit_in_orig
    · simp [h_lit_no_var]

  -- And it's still satisfied by the assignment
  exact ⟨lit, h_lit_in_filtered, h_lit_satisfied⟩

/--
**Satisfiable Nonterminal Formulas Have Preserving Operations**: Every satisfiable nonterminal
formula admits a variable assignment that preserves satisfiability.

This fundamental mathematical property shows that satisfiable formulas can always be
simplified through variable assignment while maintaining satisfiability.
-/
theorem satisfiable_nonterminal_has_preserving_assignment {Var : Type} [DecidableEq Var]
    (formula : Formula Var)
    (h_satisfiable : formula.IsSatisfiable)
    (h_nonterminal : formula.isNonterminal = true) :
    ∃ (var : Var) (value : Bool),
      formula.containsVariable var = true ∧
      (formula.setVariable var value).IsSatisfiable := by
  -- Extract the satisfying assignment
  unfold Formula.IsSatisfiable at h_satisfiable
  obtain ⟨assignment, h_assignment_satisfies⟩ := h_satisfiable

  -- Get a variable from the nonterminal formula
  obtain ⟨var, h_var_in_formula⟩ := nonterminal_contains_variable formula h_nonterminal

  -- Set this variable to its value in the satisfying assignment
  let value := assignment var
  exact ⟨var, value, h_var_in_formula, by
    unfold Formula.IsSatisfiable
    exact ⟨assignment, setVariable_preserves_satisfiability_under_witness formula assignment var h_assignment_satisfies⟩⟩
