(*
 * Algebraic Optimization — Phase 3 Block Simulation
 *
 * Lifts per-instruction simulation (ao_transform_inst) to block-level
 * simulation using analysis_block_sim_univ.
 *
 * Key insight: ao_transform_block = analysis_block_transform with
 * appropriate lattice instantiation (lattice = num, value = index).
 *
 * TOP-LEVEL:
 *   ao_phase3_block_sim — Phase 3 per-block lift_result simulation
 *)

Theory algebraicOptBlockSim
Ancestors
  algebraicOptDefs algebraicOptPeepholeSim algebraicOptResolveSim
  analysisSimDefs analysisSimProofsBase
  stateEquiv stateEquivProps
  execEquivParamProps
  venomExecSemantics venomState venomInst venomWf
  dfAnalyzeDefs indexedLists
  finite_map

(* ===== Lattice construction =====
 *
 * We need df_at bottom result bb.bb_label i = i for all valid i.
 * Construct result with ds_inst mapping (lbl, i) |-> i for all i.
 *)

(* Build a df_state where ds_inst(lbl, i) = i for i < n *)
Definition idx_df_state_def:
  idx_df_state lbl n : num df_state =
    <| ds_inst := FUN_FMAP (\p. SND p)
         (IMAGE (\i. (lbl, i)) (count n));
       ds_boundary := FEMPTY |>
End

Triviality idx_df_state_at[local]:
  !lbl n i. i < n ==>
    df_at 0 (idx_df_state lbl n) lbl i = i
Proof
  rw[df_at_def, idx_df_state_def] >>
  `FINITE (IMAGE (\i. (lbl, i)) (count n))` by simp[] >>
  `(lbl, i) IN IMAGE (\i. (lbl, i)) (count n)` by
    (simp[] >> qexists_tac `i` >> simp[]) >>
  simp[finite_mapTheory.FLOOKUP_FUN_FMAP]
QED

(* ===== Transform equivalence =====
 *
 * analysis_block_transform 0 (idx_df_state lbl n) f bb
 * = ao_transform_block mid dfg ra targets bb
 * when f = \v inst. ao_transform_inst mid dfg ra lbl v targets inst
 * and n >= LENGTH bb.bb_instructions
 *)
Triviality transform_eq[local]:
  !mid dfg ra targets bb.
    let lbl = bb.bb_label in
    let n = LENGTH bb.bb_instructions in
    let f = \v inst. ao_transform_inst mid dfg ra lbl v targets inst in
    analysis_block_transform 0 (idx_df_state lbl n) f bb =
    ao_transform_block mid dfg ra targets bb
Proof
  rw[LET_THM, analysis_block_transform_def, ao_transform_block_def] >>
  `FLAT (MAPi (\idx inst.
     ao_transform_inst mid dfg ra bb.bb_label
       (df_at 0 (idx_df_state bb.bb_label (LENGTH bb.bb_instructions))
          bb.bb_label idx) targets inst) bb.bb_instructions) =
   FLAT (MAPi (\idx inst.
     ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
       bb.bb_instructions)` suffices_by simp[] >>
  AP_TERM_TAC >>
  irule MAPi_CONG' >> simp[] >>
  rw[] >> simp[idx_df_state_at]
QED

(* ===== Per-instruction simulation =====
 *
 * This is the key assumption. It says: for well-formed instructions,
 * executing the original instruction relates to executing the transformed
 * instruction list via lift_result.
 *
 * Currently cheated in algebraicOptProofsScript.sml (ao_transform_inst_sim).
 * We re-state it here as the main hypothesis of our block sim theorem.
 *)

(* ===== Operand agreement under state_equiv =====
 *
 * If x NOTIN fv, then state_equiv fv s1 s2 ==> lookup_var x s1 = lookup_var x s2
 *)
Triviality operand_agreement[local]:
  !fv inst x s1 s2.
    MEM (Var x) inst.inst_operands /\
    x NOTIN fv /\
    state_equiv fv s1 s2 ==>
    lookup_var x s1 = lookup_var x s2
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* ===== Main theorem: Phase 3 block simulation ===== *)

Theorem ao_phase3_block_sim:
  !fv mid dfg ra targets bb.
    (* Per-instruction simulation holds *)
    analysis_inst_simulates
      (state_equiv fv) (execution_equiv fv) (\v s. T)
      (\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst) /\
    (* All instructions are well-formed *)
    EVERY inst_wf bb.bb_instructions /\
    (* Operands of original block instructions are not in fv *)
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fv)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (ao_transform_block mid dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Rewrite goal: ao_transform_block → analysis_block_transform *)
  ONCE_REWRITE_TAC
    [GSYM (SIMP_RULE (srw_ss()) [LET_THM] transform_eq)] >>
  (* Apply analysis_block_sim_univ *)
  qspecl_then
    [`state_equiv fv`, `execution_equiv fv`,
     `\(v:num) (s:venom_state). T`,
     `\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst`,
     `bb`, `0`, `idx_df_state bb.bb_label (LENGTH bb.bb_instructions)`]
    mp_tac analysis_block_sim_univ >>
  impl_tac
  >- (rpt conj_tac
      >- (* valid_state_rel *)
         simp[state_equiv_execution_equiv_valid_state_rel]
      >- (* R_ok transitive *)
         metis_tac[state_equiv_trans]
      >- (* R_term transitive *)
         metis_tac[execution_equiv_trans]
      >- (* analysis_inst_simulates *)
         first_assum ACCEPT_TAC
      >- (* EVERY inst_wf *)
         first_assum ACCEPT_TAC
      >- (* operand agreement *)
         (rpt strip_tac >>
          `x NOTIN fv` by metis_tac[] >>
          fs[state_equiv_def, execution_equiv_def])
      >- (* soundness — trivially T *)
         simp[])
  >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* ===== Invariant-carrying block simulation ===== *)

(* Like ao_phase3_block_sim but with state_inv.
   Per-instruction sim requires BOTH sound AND state_inv.
   state_inv is preserved through step_inst and state_equiv. *)
Theorem ao_phase3_block_sim_inv:
  !fv mid dfg ra targets bb (state_inv : venom_state -> bool).
    (* Per-instruction simulation under state_inv *)
    (!fuel ctx v inst s.
       state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (step_inst fuel ctx inst s)
         (run_insts fuel ctx
           (ao_transform_inst mid dfg ra bb.bb_label v targets inst) s)) /\
    inst_transform_structural
      (\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst) /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fv) /\
    (* state_inv preserved through step_inst from this block *)
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\ inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (* state_inv preserved through state_equiv *)
    (!s1 s2. state_equiv fv s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ state_inv s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (ao_transform_block mid dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Rewrite ao_transform_block to analysis_block_transform *)
  `ao_transform_block mid dfg ra targets bb =
   analysis_block_transform 0
     (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
     (\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst) bb` by
    (simp[analysis_block_transform_def, ao_transform_block_def] >>
     `MAPi (\idx inst. ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
          bb.bb_instructions =
      MAPi (\idx inst. ao_transform_inst mid dfg ra bb.bb_label
          (df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
             bb.bb_label idx) targets inst) bb.bb_instructions`
       suffices_by simp[] >>
     irule MAPi_CONG' >> simp[] >> rpt strip_tac >>
     `n < SUC (LENGTH bb.bb_instructions)` by simp[] >>
     simp[idx_df_state_at]) >>
  ASM_REWRITE_TAC [] >>
  qspecl_then
    [`state_equiv fv`, `execution_equiv fv`,
     `\(v:num) (s:venom_state). T`, `state_inv`,
     `\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst`,
     `bb`, `0`, `idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))`,
     `\(ctx:'b) (inst:instruction) v. SUC v`, `ARB`]
    mp_tac analysis_block_sim_inv >>
  impl_tac
  >- (rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[])
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >>
          `x NOTIN fv` by res_tac >>
          fs[state_equiv_def, execution_equiv_def])
      >- simp[transfer_sound_wf_def]
      >- simp[]
      >- (rpt strip_tac >> simp[idx_df_state_at])
      >- (rpt strip_tac >> res_tac)
      >- (rpt strip_tac >> res_tac)) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

val _ = export_theory();
