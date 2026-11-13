(* Residual mem2var frame. Variables and promoted memory are independently
   related; instruction indices and call-entry FMP were already ignored.
   All remaining components, including future fields, are retained.
   TOP-LEVEL: m2v_frame; reconstruction, projection and update boundaries. *)
Theory mem2varFrame
Ancestors
  venomState finite_map mem2varDefs

Definition m2v_frame_def:
  m2v_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_memory := []; vs_inst_idx := 0;
    vs_call_entry_fmp := 0w |>
End

Theorem m2v_frame_idempotent[simp]:
  m2v_frame (m2v_frame s) = m2v_frame s
Proof
  simp[m2v_frame_def]
QED

Theorem m2v_frame_erased_updates[simp]:
  m2v_frame (s with vs_vars := vars) = m2v_frame s /\
  m2v_frame (s with vs_memory := mem) = m2v_frame s /\
  m2v_frame (s with vs_inst_idx := idx) = m2v_frame s /\
  m2v_frame (s with vs_call_entry_fmp := fmp) = m2v_frame s /\
  m2v_frame (update_var x v s) = m2v_frame s
Proof
  simp[m2v_frame_def, update_var_def]
QED

Theorem m2v_frame_reconstruct:
  (m2v_frame s with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_inst_idx := s.vs_inst_idx; vs_call_entry_fmp := s.vs_call_entry_fmp |>) = s
Proof
  simp[m2v_frame_def]
QED

Theorem m2v_frame_eq_reconstruct:
  m2v_frame s1 = m2v_frame s2 <=>
  (s1 with <| vs_vars := s2.vs_vars; vs_memory := s2.vs_memory;
    vs_inst_idx := s2.vs_inst_idx; vs_call_entry_fmp := s2.vs_call_entry_fmp |>) = s2
Proof
  simp[m2v_frame_def, venom_state_component_equality]
QED

Theorem m2v_frame_projection:
  (!s. project (m2v_frame s) = project s) /\
  m2v_frame s1 = m2v_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem m2v_frame_update:
  (!s. m2v_frame (update s) = update_frame (m2v_frame s)) /\
  m2v_frame s1 = m2v_frame s2 ==>
  m2v_frame (update s1) = m2v_frame (update s2)
Proof
  metis_tac[]
QED

(*
 * m2v_equiv: State equivalence ignoring vs_memory.
 *
 * mem2var promotes MSTORE→ASSIGN, so memory genuinely differs after
 * transformation (alloca regions are not written in the transformed code).
 * This relation captures everything that IS preserved:
 *   - All variables (except fresh alloca promotion vars)
 *   - Residual m2v_frame (ignores memory, index and call-entry FMP)
 *   - Both block labels (usable as both R_ok and R_term in lift_result)
 *
 * The `vars` parameter excludes fresh variables introduced by promotion
 * (the alloca_N_M naming scheme). These variables exist only in the
 * transformed state.
 *
 * Allocation state and the other three FMP fields remain compared.
 * Clearing fields in the mask does not constrain their original values.
 *)
Definition m2v_equiv_def:
  m2v_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    m2v_frame s1 = m2v_frame s2
End

(* Inter-block invariant:
   1. m2v_equiv: all non-fresh variables and non-memory fields agree
   2. Memory agreement outside promoted alloca regions
   3. Sync: each written promoted variable tracks the alloca memory cell *)
Definition m2v_inv_def:
  m2v_inv fn s1 s2 <=>
    m2v_equiv (m2v_fresh_vars fn) s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!i. ~in_promoted_region fn s1 i ==>
         mem_byte i s1 = mem_byte i s2) /\
    (!ao pvar sz.
       MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
       !addr. lookup_var ao s1 = SOME addr ==>
         IS_SOME (lookup_var pvar s2) ==>
         lookup_var pvar s2 = SOME (mload (w2n addr) s1))
End
