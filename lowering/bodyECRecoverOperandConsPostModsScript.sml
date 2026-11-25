(* Compose an ECRecover operand read with its landed tail at one horizon. *)
Theory bodyECRecoverOperandConsPostMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprSimPrecompiles
  wordArgsPtr exprSimWordArgs bodyPtrDefs exprLoweringProps freshWrites ptrDiscipline list

val typed_at = ``\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                              value_has_type tv v``;

Theorem ecrecover_operand_cons_post_mods:
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\ (^typed_at) e v /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ci_mono s1 sm /\
  typed_args_post H ctx func cenv cx mid s1 t ee rest ys vs u /\
  LIST_REL (^typed_at) rest vs /\ immutable_frame_mods func cenv cx ee u /\
  u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G tn /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) ys /\
  EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at sm z)) ys ==>
  typed_args_post H ctx func cenv cx es sa s0 ee (e::rest) (x::ys) (v::vs) u /\
  LIST_REL (^typed_at) (e::rest) (v::vs) /\ immutable_frame_mods func cenv cx ee u /\
  u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) (x::ys) /\
  EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at sm z)) (x::ys)
Proof
  BETA_TAC >> simp[expr_post_mods_def] >> strip_tac >>
  conj_tac
  >- (drule_all typed_args_post_cons >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by fs[ptr_val_ok_def] >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    (Cases_on `x` >>
     fs[op_prov_def, op_taint_def] >>
     qpat_assum `ghost_kept_at _ _ mid _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     strip_tac >> first_x_assum drule >> simp[op_taint_def]) >>
  simp[] >>
  drule_then assume_tac expr_post_frame >>
  drule_all_then ACCEPT_TAC ghost_kept_at_wb_trans
QED
