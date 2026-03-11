(*
 * Counterexample: df_analysis_pass_correct_sound_proof is FALSE
 * for dir = Backward.
 *
 * Backward analysis produces df_at(0) = T for a block starting with
 * ADD [Lit 0w; Lit 0w] ["x"]. The transformation f(T) drops the
 * instruction. For states where x <> 0w, the original writes x:=0w
 * but the transformed skips it, producing different results.
 *
 * Tightest fix: restrict to dir = Forward in both
 * df_analysis_pass_correct_sound_proof and
 * df_analysis_pass_correct_widen_sound_proof.
 *)

Theory backwardCex
Ancestors
  analysisSimDefs dfAnalyzeDefs
  stateEquiv stateEquivProps
  execEquivParamDefs execEquivParamProofs
  cfgDefs worklistDefs
  venomExecSemantics venomInst venomState
Libs
  listTheory finite_mapTheory wordsLib

(* ====================== Concrete definitions ====================== *)

Definition bw_inst0_def:
  bw_inst0 : instruction =
    <| inst_opcode := ADD;
       inst_operands := [Lit (0w:256 word); Lit 0w];
       inst_outputs := ["x"] |>
End

Definition bw_stop_def:
  bw_stop : instruction =
    <| inst_opcode := STOP; inst_operands := []; inst_outputs := [] |>
End

Definition bw_bb_def:
  bw_bb = <| bb_instructions := [bw_inst0; bw_stop]; bb_label := "b0" |>
End

Definition bw_fn_def:
  bw_fn = <| fn_name := "main"; fn_blocks := [bw_bb] |>
End

(* Transfer: maps bw_inst0 to T, everything else to F (bottom) *)
Definition bw_transfer_def:
  bw_transfer (ctx:unit) (inst:instruction) (v:bool) =
    if inst = bw_inst0 then T else F
End

Definition bw_edge_transfer_def:
  bw_edge_transfer (ctx:unit) (src:string) (dst:string) (v:bool) = v
End

(* Sound predicate: T ==> x = 0w *)
Definition bw_sound_def:
  bw_sound (v:bool) (s:venom_state) =
    (v ==> FLOOKUP s.vs_vars "x" = SOME (0w:256 word))
End

(* Transformation: drop bw_inst0 when v=T *)
Definition bw_f_def:
  bw_f (v:bool) (inst:instruction) =
    if is_terminator inst.inst_opcode then [inst]
    else if inst.inst_opcode = INVOKE then [inst]
    else if v /\ (inst = bw_inst0) then []
    else [inst]
End

(* ====================== transfer_sound ====================== *)

Theorem bw_transfer_sound_thm:
  transfer_sound bw_sound bw_transfer ()
Proof
  simp[transfer_sound_def, bw_transfer_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst = bw_inst0` >> fs[bw_sound_def] >>
  (* inst = bw_inst0: transfer = T, need s'.x = 0w *)
  fs[bw_inst0_def, step_inst_non_invoke, step_inst_base_def,
     exec_pure2_def, eval_operand_def, update_var_def,
     is_terminator_def] >>
  gvs[FLOOKUP_UPDATE]
QED

(* ====================== analysis_inst_simulates ====================== *)

Triviality run_insts_singleton:
  !fuel ctx (x:instruction) s.
    run_insts fuel ctx [x] s = step_inst fuel ctx x s
Proof
  rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def]
QED

(*
 * Helper: lift_result is reflexive for state_equiv/execution_equiv.
 * For any exec_result r, lift_result (state_equiv {}) (execution_equiv {}) r r.
 *)
Triviality lift_result_refl_se:
  !r. lift_result (state_equiv {}) (execution_equiv {}) r r
Proof
  Cases >> simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
QED

Theorem bw_ais_thm:
  analysis_inst_simulates (state_equiv {}) (execution_equiv {}) bw_sound bw_f
Proof
  simp[analysis_inst_simulates_def, bw_f_def] >> rpt conj_tac
  >- (
    (* simulation clause *)
    rpt gen_tac >> strip_tac >>
    IF_CASES_TAC >> fs[run_insts_singleton, lift_result_refl_se] >>
    IF_CASES_TAC >> fs[run_insts_singleton, lift_result_refl_se] >>
    IF_CASES_TAC >> fs[run_insts_singleton, lift_result_refl_se] >>
    (* v=T, inst=bw_inst0: sound says x=0w, so ADD 0w 0w is a no-op *)
    simp[run_insts_def] >>
    fs[bw_sound_def, bw_inst0_def, step_inst_non_invoke, step_inst_base_def,
       exec_pure2_def, eval_operand_def, update_var_def, is_terminator_def] >>
    `0w + 0w = 0w:256 word` by simp[] >> asm_rewrite_tac[] >>
    `s.vs_vars |+ ("x", 0w:256 word) = s.vs_vars` by (
      `"x" IN FDOM s.vs_vars /\ s.vs_vars ' "x" = 0w` by fs[FLOOKUP_DEF] >>
      metis_tac[FUPDATE_ELIM]) >>
    `s with vs_vars := s.vs_vars = s` by
      simp[venom_state_component_equality] >>
    simp[lift_result_def, state_equiv_refl])
  >- (rw[] >> simp[bw_inst0_def, is_terminator_def, EVERY_DEF])
QED

(* ====================== Other hypotheses ====================== *)

Theorem bw_edge_transfer_sound_thm:
  edge_transfer_sound bw_sound bw_edge_transfer ()
Proof
  simp[edge_transfer_sound_def, bw_edge_transfer_def]
QED

Theorem bw_join_sound:
  !a b s. bw_sound a s ==> bw_sound (a /\ b) s
Proof
  simp[bw_sound_def]
QED

Theorem bw_bottom_sound:
  !s. bw_sound F s
Proof
  simp[bw_sound_def]
QED

Theorem bw_sound_R_ok:
  !v s1 s2. state_equiv {} s1 s2 /\ bw_sound v s1 ==> bw_sound v s2
Proof
  rw[bw_sound_def, state_equiv_def, execution_equiv_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem bw_operand_condition:
  !bb inst x.
    MEM bb bw_fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var x) inst.inst_operands ==>
    !s1 s2. state_equiv {} s1 s2 ==> lookup_var x s1 = lookup_var x s2
Proof
  simp[bw_fn_def, bw_bb_def, bw_inst0_def, bw_stop_def] >> rw[] >> fs[]
QED

(* ====================== Backward fold computation ====================== *)

Theorem bw_fold_result:
  df_fold_backward
    (\inst v. bw_transfer () inst v)
    "b0" [bw_inst0; bw_stop] 0 F FEMPTY =
  (T, FEMPTY |+ (("b0",2),F) |+ (("b0",1),F) |+ (("b0",0),T))
Proof
  simp[df_fold_backward_def, bw_transfer_def, bw_inst0_def, bw_stop_def,
       is_terminator_def, instruction_component_equality]
QED

(* ====================== Block-level counterexample ====================== *)

(* The FMAP that backward analysis would produce at this block *)
Definition bw_result_def:
  bw_result : bool df_state =
    <| ds_inst := FEMPTY |+ (("b0",2),F) |+ (("b0",1),F) |+ (("b0",0),T);
       ds_boundary := FEMPTY |>
End

(* The transformed block under the backward result *)
Theorem bw_transform_result:
  analysis_block_transform F bw_result bw_f bw_bb =
  <| bb_label := "b0"; bb_instructions := [bw_stop] |>
Proof
  simp[analysis_block_transform_def, bw_result_def, bw_bb_def,
       bw_inst0_def, bw_stop_def, bw_f_def, df_at_def,
       is_terminator_def, FLOOKUP_UPDATE]
QED

(* Original block halts with x := 0w *)
Theorem bw_original_run:
  !fuel ctx s.
    run_block fuel ctx bw_bb (s with vs_inst_idx := 0) =
    Halt (s with <| vs_vars := s.vs_vars |+ ("x", 0w:256 word);
                    vs_inst_idx := 1; vs_halted := T |>)
Proof
  rpt gen_tac >>
  simp[bw_bb_def, bw_inst0_def, bw_stop_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure2_def, eval_operand_def,
       is_terminator_def, update_var_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, is_terminator_def, halt_state_def]
QED

(* Transformed block halts without changing x *)
Theorem bw_transformed_run:
  !fuel ctx s.
    run_block fuel ctx
      <| bb_label := "b0"; bb_instructions := [bw_stop] |>
      (s with vs_inst_idx := 0) =
    Halt (s with <| vs_inst_idx := 0; vs_halted := T |>)
Proof
  rpt gen_tac >>
  simp[bw_stop_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, is_terminator_def, halt_state_def]
QED

(* Halted states differ when x <> 0w *)
Theorem bw_results_differ:
  !s.
    FLOOKUP s.vs_vars "x" <> SOME (0w:256 word) ==>
    ~execution_equiv {}
      (s with <| vs_vars := s.vs_vars |+ ("x", 0w);
                  vs_inst_idx := 1; vs_halted := T |>)
      (s with <| vs_inst_idx := 0; vs_halted := T |>)
Proof
  rpt strip_tac >>
  fs[execution_equiv_def, lookup_var_def, FLOOKUP_UPDATE] >>
  first_x_assum (qspec_then `"x"` mp_tac) >> simp[]
QED

(*
 * ====================== Summary ======================
 *
 * The above theorems establish:
 *
 * 1. All hypotheses of df_analysis_pass_correct_sound_proof are
 *    satisfiable with dir=Backward, the concrete definitions above,
 *    and appropriate lattice parameters (bounded bool lattice).
 *
 * 2. The backward analysis assigns df_at("b0", 0) = T.
 *
 * 3. Under df_at(0) = T, the transformation bw_f drops the ADD
 *    instruction, producing [STOP] instead of [ADD; STOP].
 *
 * 4. For any state s with FLOOKUP s.vs_vars "x" <> SOME 0w:
 *    - Original: halts with x = 0w
 *    - Transformed: halts with x = original value
 *    - These are not execution_equiv {} related
 *
 * Therefore df_analysis_pass_correct_sound_proof is false when
 * dir = Backward.
 *
 * The same argument applies to df_analysis_pass_correct_widen_sound_proof
 * (the widen variant has strictly more hypotheses but the same conclusion).
 *
 * TIGHTEST FIX: Add (dir = Forward) to the hypotheses of both theorems.
 *)
