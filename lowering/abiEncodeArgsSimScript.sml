Theory abiEncodeArgsSim
Ancestors
  abiEncodeMaterialize abiEncodeArgsScopes abiEncodeArgsWindows
  compileEnv exprSim exprSimHyps exprSimWordArgs

Definition abi_args_post_def:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s <=>
    stmt_state_rel ctx func ce cx es' s /\
    LENGTH args = LENGTH vs /\
    LIST_REL (\op ev.
      expr_val_rel cx (expr_type (FST ev)) (SND ev) op s /\
      expr_val_at ce cx (expr_type (FST ev)) sa sb es' (SND ev) op s)
      ops (ZIP (args,vs)) /\
    wb_frame ce es sa s0 s
End

Definition abi_args_ready_def:
  abi_args_ready ctx func ce cx Inv [] = T /\
  abi_args_ready ctx func ce cx Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func ce cx (expr_type e) e es /\
       expr_vv_sim ctx func ce cx (expr_type e) e es /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
          expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
          Inv es' /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
          (~is_word_type (expr_type e) /\ exprs_can_mutate ce args ==>
           ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                value_has_type tv v /\ val_wf tv v /\
                type_memory_bytes ce (expr_type e) = type_memory_size tv /\
                type_memory_size tv < 2 ** 64 /\
                type_memory_size tv + 64 < dimword (:256)))) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                         read_result cx tv s1 = (INL v,t1)) ==>
       abi_args_ready ctx func ce cx Inv args))
End

Theorem abi_args_post_nil:
  abi_args_post ctx func ce cx es sa sb s0 es' [] ops vs s <=>
    ops = [] /\ vs = [] /\ stmt_state_rel ctx func ce cx es' s /\
    wb_frame ce es sa s0 s
Proof
  Cases_on `vs` >> simp[abi_args_post_def] >> metis_tac[]
QED

Theorem abi_args_post_cons:
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) s <=>
    expr_val_rel cx (expr_type e) v op s /\
    expr_val_at ce cx (expr_type e) sa sb es' v op s /\
    abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s
Proof
  simp[abi_args_post_def] >> metis_tac[]
QED

Theorem abi_args_post_lengths:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s ==>
    LENGTH args = LENGTH vs /\ LENGTH ops = LENGTH args
Proof
  simp[abi_args_post_def] >> rpt strip_tac >>
  drule listTheory.LIST_REL_LENGTH >> simp[]
QED

Theorem abi_args_ready_tail:
  abi_args_ready ctx func ce cx Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) ==>
  abi_args_ready ctx func ce cx Inv args
Proof
  simp[abi_args_ready_def] >> rpt strip_tac >> first_x_assum irule >>
  drule eval_expr_read_INL >> metis_tac[]
QED

(* Readiness premise ledger (applicability remains a separate obligation).
   - head simulations: exprs_case_def at expr_type e.
   - result admissibility and next invariant: expr_body_pre_eval, together
     with the unchanged body-pre environment and call-safety premises.
   - source scope domains: eval_expr_preserves_scopes_dom and
     vyperState.read_result_state (reading never changes source state).
   - evaluated type and value_has_type: expr_body_pre_eval's
     expr_result_typed, unfolded through value_runtime_typed, and the
     environment/get_tenv agreement in expr_sim_inv.
   - val_wf: valueEncodingTyping.value_has_type_val_wf.
   - layout equality and size < 2**64: expr_body_pre_copy_ok.
   - size + 64 < dimword(:256): arithmetic consequence of size < 2**64.
   None of these items permits literal ABI has_type or declared capacity
   to be inferred from expr_val_at. *)

Theorem abi_args_read_state:
  read_result cx result es = (res,es') ==> es' = es
Proof
  metis_tac[vyperStateTheory.read_result_state]
QED

Theorem abi_args_capture_size:
  n < 2 ** 64 ==> n + 64 < dimword (:256)
Proof
  simp[wordsTheory.dimword_def] >> decide_tac
QED

Theorem abi_args_local_type_coherent:
  expr_sim_inv ce cx env es /\ lookup_scopes name es.scopes = SOME entry ==>
  ?ty. ce.ce_var_type name = SOME ty /\
       evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  simp[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
  rpt strip_tac >>
  `IS_SOME (FLOOKUP env.var_types name)` by metis_tac[] >>
  Cases_on `FLOOKUP env.var_types name` >> gvs[] >> metis_tac[]
QED

Theorem abi_args_dynamic_local_type:
  expr_sim_inv ce cx env es /\ lookup_scopes name es.scopes = SOME entry /\
  dynarray_local ce name ==>
  ?etv n. entry.type = ArrayTV etv (Dynamic n)
Proof
  strip_tac >> drule_all abi_args_local_type_coherent >> strip_tac >>
  gvs[dynarray_local_def] >>
  Cases_on `ty` >> gvs[dynarray_type_def, vyperValueTheory.evaluate_type_def,
                         AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_args_local_region_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es st s0 s1 /\
  local_region ce es.scopes s0 name b sz ==>
  mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  strip_tac >>
  `locals_kept ce es s0 s1` by gvs[wb_frame_def] >>
  Cases_on `dynarray_local ce name`
  >- (qpat_assum `local_region _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [local_region_def]) >>
      drule_all abi_args_dynamic_local_type >> strip_tac >>
      `lookup_var p s1 = SOME w` by
        (gvs[wb_frame_def, local_ptrs_reserved_def] >> metis_tac[]) >>
      `local_ptrs_rel func ce es.scopes s0 /\
       local_ptrs_rel func ce es.scopes s1` by
        gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
      drule_all local_ptrs_rel_value_at >> strip_tac >>
      `val_in_memory entry.type entry.value (w2n w) s0.vs_memory` by
        metis_tac[local_ptrs_rel_value_at] >>
      `val_wf entry.type entry.value` by
        (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
      `value_has_type entry.type entry.value` by
        (irule vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type >>
         qexistsl [`name`, `es`] >> gvs[expr_sim_inv_def]) >>
      `mem_word_at b s1.vs_memory = mem_word_at b s0.vs_memory` by
        (Cases_on `entry.value` >>
         gvs[valueEncodingTheory.val_wf_def, valueEncodingTheory.val_in_memory_def,
             vyperTypingTheory.value_has_type_inv] >>
         rename1 `entry.value = ArrayV av` >>
         Cases_on `av` >> gvs[valueEncodingTheory.val_wf_def,
                              valueEncodingTheory.val_in_memory_def]) >>
      `32 <= sz` by gvs[valueEncodingTheory.type_memory_size_def] >>
      `mem_bytes_at b 32 s1.vs_memory = mem_bytes_at b 32 s0.vs_memory` by
        simp[valueEncodingProofsTheory.mem_bytes_at_word] >>
      `mem_bytes_at (b + 32) (sz - 32) s1.vs_memory =
       mem_bytes_at (b + 32) (sz - 32) s0.vs_memory` by
        (gvs[locals_kept_def] >> first_x_assum irule >>
         qexistsl [`w2n w`, `name`, `sz`] >> simp[]) >>
      `sz = 32 + (sz - 32)` by decide_tac >>
      metis_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded]) >>
  gvs[locals_kept_def] >> first_x_assum irule >>
  qexistsl [`b`, `name`, `sz`] >> simp[]
QED

Theorem abi_args_local_window_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es st s0 s1 /\
  local_region ce es.scopes s0 name b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s1.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac >> drule_all abi_args_local_region_kept >>
  disch_then (mp_tac o GSYM) >>
  disch_then (strip_assume_tac o MATCH_MP valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  simp[]
QED

Theorem abi_args_operand_kept:
  wb_frame ce es st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s1 = SOME w
Proof
  strip_tac >> irule exprSimOpsTheory.eval_operand_frame >>
  simp[] >> qexistsl [`st`, `s0`] >> gvs[wb_frame_def]
QED

Theorem abi_args_location_kept:
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\ local_ptrs_reserved ce st /\
  wb_frame ce es st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_at ce cx ty sa sb es' v op s1
Proof
  strip_tac >> rewrite_tac[expr_val_at_def] >> rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  `eval_operand op s1 = SOME w` by metis_tac[abi_args_operand_kept] >>
  simp[]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >>
      conj_tac >- (gvs[wb_frame_def] >> metis_tac[]) >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> qexists `n` >>
      irule exprSimOpsTheory.local_region_frame >>
      conj_tac
      >- (qexists `func` >>
          gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
      qexistsl [`st`, `es'.scopes`, `s1`] >> gvs[wb_frame_def])
  >- (disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[] >>
      irule exprSimOpsTheory.local_region_frame_fwd >>
      qexistsl [`s0`, `st`, `es.scopes`] >> gvs[wb_frame_def])
  >> simp[]
QED

Theorem abi_args_value_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es st s0 s1 /\
  sb.cs_next_id <= st.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_rel cx ty v op s0 /\ expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_rel cx ty v op s1
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
      simp[expr_val_rel_def] >> rpt strip_tac >>
      qexists `w` >> simp[] >> irule abi_args_operand_kept >> metis_tac[]) >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `eval_operand op s1 = SOME w` by
    (irule abi_args_operand_kept >> metis_tac[]) >>
  rewrite_tac[expr_val_rel_def] >> qexists `w` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> irule val_in_memory_footprint_agree >>
  simp[] >> qexists `s0.vs_memory` >> simp[]
  >- (`mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >>
         conj_tac >- (rpt strip_tac >> metis_tac[]) >>
         qexists `aid` >> simp[]) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      simp[])
  >- (sym_tac >> irule abi_args_local_window_kept >> metis_tac[])
  >> simp[valueEncodingTheory.mem_bytes_at_def]
QED

Theorem abi_args_captured_value_kept:
  wb_frame ce es st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_val_rel cx ty v op s0 /\ val_wf tv v /\
  eval_operand op s0 = SOME w /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < st.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
              b + sz <= lb \/ lb + lsz <= b) ==>
  expr_val_rel cx ty v op s1
Proof
  strip_tac >> irule expr_val_rel_footprint_agree >>
  simp[] >> qexistsl [`s0`, `w`] >> simp[] >> reverse conj_tac
  >- (irule abi_args_operand_kept >> metis_tac[]) >>
  `mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory` by
    (gvs[wb_frame_def] >> first_x_assum irule >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     qexists `aid` >> simp[]) >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> simp[]
QED

Theorem abi_args_nil_sim:
  frag_exec ctx sa sa (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. abi_args_post ctx func ce cx es sa sa s0 es [] [] [] s)
    (wb_args_exit (INL []))
Proof
  irule fragExecTheory.frag_exec_refl >> simp[abi_args_post_def, wb_frame_refl] >> metis_tac[]
QED

Theorem abi_args_ready_head:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es ==>
  expr_sim ctx func ce cx (expr_type e) e es /\
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
     expr_res_ok res) /\
  (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
     Inv es' /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
     (~is_word_type (expr_type e) /\ exprs_can_mutate ce args ==>
      ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
           value_has_type tv v /\ val_wf tv v /\
           type_memory_bytes ce (expr_type e) = type_memory_size tv /\
           type_memory_size tv < 2 ** 64 /\
           type_memory_size tv + 64 < dimword (:256)))
Proof
  simp[abi_args_ready_def] >> metis_tac[]
QED

Theorem abi_args_compile_mono:
  !args ce st.
    ci_mono st (SND (compile_abi_encode_args compile_expr ce args st))
Proof
  Induct >> rpt gen_tac >> rewrite_tac[exprLoweringTheory.compile_abi_encode_args_def] >>
  simp[exprLoweringPropsTheory.ci_mono_comp_return] >>
  ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
  >- simp[cj 1 exprLoweringPropsTheory.compile_expr_ci_mono] >>
  rpt strip_tac >> ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[exprLoweringPropsTheory.ci_mono_compile_materialize_vv,
                           exprLoweringPropsTheory.ci_mono_unwrap_value]) >>
  rpt strip_tac >> ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
  >- simp[] >>
  simp[exprLoweringPropsTheory.ci_mono_comp_return]
QED

Theorem abi_args_location_end_mono:
  sm.cs_next_id <= sb.cs_next_id /\ expr_val_at ce cx ty sa sm es v op s ==>
  expr_val_at ce cx ty sa sb es v op s
Proof
  simp[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> qexists `w` >> simp[]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[]
QED

Theorem abi_args_post_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  abi_args_post ctx func ce cx es sm sb s0 es' args ops vs s /\
  wb_frame ce es sa s0 s ==>
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s
Proof
  simp[abi_args_post_def] >> rpt strip_tac >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  irule expr_val_at_start_mono >> metis_tac[]
QED

Theorem abi_args_post_cons_frame:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  expr_val_rel cx (expr_type e) v op u /\
  expr_val_at ce cx (expr_type e) sa sb es' v op u ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >> rewrite_tac[abi_args_post_cons] >> simp[] >>
  `wb_frame ce es sa s0 u` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl [`es1`, `sm`, `t`] >>
         gvs[abi_args_post_def] >> metis_tac[expr_post_frame]) >>
     qexistsl [`ctx`, `cx`, `func`] >> simp[]) >>
  qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[abi_args_post_def] >> strip_tac >> simp[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> irule expr_val_at_start_mono >> metis_tac[]
QED
