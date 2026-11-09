Theory abiEncodeArgsSim
Ancestors
  abiEncodeMaterialize abiEncodeArgsScopes abiEncodeArgsWindows abiDecoderReentry
  compileEnv exprSimDefs exprSimProps loweringPosts exprSimHyps exprSimWordArgs abiArgsLabelObserver exprOperandVar
  abiArgsLabelBoundary

Definition abi_args_post_def:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s <=>
    stmt_state_rel ctx func ce cx es' s /\
    LENGTH args = LENGTH vs /\
    LIST_REL (\op ev.
      expr_val_rel cx (lowered_value_type ce (FST ev)) (SND ev) op s /\
      expr_val_at ce cx (lowered_value_type ce (FST ev)) sa sb es' (SND ev) op s)
      ops (ZIP (args,vs)) /\
    wb_frame ce es es' sa s0 s
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
          (~is_word_type (expr_type e) ==>
           ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
                value_has_type tv v /\ val_wf tv v /\
                type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
                type_memory_size tv < 2 ** 64 /\
                type_memory_size tv + 64 < dimword (:256)))) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                         read_result cx tv s1 = (INL v,t1)) ==>
       abi_args_ready ctx func ce cx Inv args))
End

Theorem abi_args_post_nil:
  abi_args_post ctx func ce cx es sa sb s0 es' [] ops vs s <=>
    ops = [] /\ vs = [] /\ stmt_state_rel ctx func ce cx es' s /\
    wb_frame ce es es' sa s0 s
Proof
  Cases_on `vs` >> simp[abi_args_post_def] >> metis_tac[]
QED

Theorem abi_args_post_cons:
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) s <=>
    expr_val_rel cx (lowered_value_type ce e) v op s /\
    expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op s /\
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
  drule exprSimSourceTheory.eval_expr_read_INL >> metis_tac[]
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
  simp[exprSimHypsDefsTheory.expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
  rpt strip_tac >>
  `IS_SOME (FLOOKUP env.var_types name)` by metis_tac[] >>
  Cases_on `FLOOKUP env.var_types name` >> gvs[] >> metis_tac[]
QED

Theorem abi_args_local_region_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  local_region ce es.scopes s0 name b sz ==>
  mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  simp[wb_frame_def, locals_kept_def] >> metis_tac[]
QED

Theorem abi_args_local_window_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  local_region ce es.scopes s0 name b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s1.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac >> drule_all abi_args_local_region_kept >> strip_tac >>
  `off = b + (off - b)` by decide_tac >>
  `off - b + len <= sz` by decide_tac >>
  metis_tac[valueEncodingPropsTheory.mem_bytes_at_translated_window]
QED

Theorem abi_args_operand_kept:
  wb_frame ce es es' st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s1 = SOME w
Proof
  strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
  simp[] >> qexistsl [`st`, `s0`] >> gvs[wb_frame_def]
QED

Theorem abi_args_location_kept_eq:
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\ local_ptrs_reserved ce st /\
  wb_frame ce es es' st s0 s1 /\
  eval_operand op s0 = eval_operand op s1 /\
  expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_at ce cx ty sa sb es' v op s1
Proof
  strip_tac >> rewrite_tac[expr_val_at_def] >> rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  `eval_operand op s1 = SOME w` by metis_tac[] >>
  simp[]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >>
      conj_tac >- (gvs[wb_frame_def] >> metis_tac[]) >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> qexists `n` >>
      irule exprSimPropsTheory.local_region_frame >>
      conj_tac
      >- (qexists `func` >>
          gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
      qexistsl [`st`, `es'.scopes`, `s1`] >> gvs[wb_frame_def])
  >- (disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[] >>
      irule exprSimPropsTheory.local_region_frame_fwd >>
      qexistsl [`s0`, `st`, `es.scopes`] >> gvs[wb_frame_def])
  >> simp[]
QED

Theorem abi_args_location_kept:
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\ local_ptrs_reserved ce st /\
  wb_frame ce es es' st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_at ce cx ty sa sb es' v op s1
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- simp[expr_val_at_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty`
  >- simp[expr_val_at_def] >>
  `?w. eval_operand op s0 = SOME w` by
    metis_tac[expr_val_at_def] >>
  `eval_operand op s0 = eval_operand op s1` by
    metis_tac[abi_args_operand_kept] >>
  irule abi_args_location_kept_eq >> metis_tac[]
QED

Theorem abi_args_value_kept_eq:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  sb.cs_next_id <= st.cs_next_id /\
  eval_operand op s0 = eval_operand op s1 /\
  expr_val_rel cx ty v op s0 /\ expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_rel cx ty v op s1
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
      simp[expr_val_rel_def] >> rpt strip_tac >>
      qexists `w` >> simp[]) >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `eval_operand op s1 = SOME w` by metis_tac[] >>
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

Theorem abi_args_value_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  sb.cs_next_id <= st.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_rel cx ty v op s0 /\ expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_rel cx ty v op s1
Proof
  strip_tac >> irule abi_args_value_kept_eq >>
  `eval_operand op s0 = eval_operand op s1` by
    (Cases_on `eval_operand op s0` >>
     gvs[expr_val_rel_def] >> metis_tac[abi_args_operand_kept]) >>
  metis_tac[]
QED

Theorem abi_args_captured_value_kept:
  wb_frame ce es es' st s0 s1 /\
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
  cheat
QED

Theorem abi_args_ready_head:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es ==>
  expr_sim ctx func ce cx (expr_type e) e es /\
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
     expr_res_ok res) /\
  (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
     Inv es' /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
     (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           value_has_type tv v /\ val_wf tv v /\
           type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
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
  wb_frame ce es es' sa s0 s ==>
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
  expr_val_rel cx (lowered_value_type ce e) v op u /\
  expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op u ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >> rewrite_tac[abi_args_post_cons] >> simp[] >>
  `wb_frame ce es es' sa s0 u` by
    (irule wb_frame_trans >>
     gvs[abi_args_post_def] >> metis_tac[expr_post_frame]) >>
  qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[abi_args_post_def] >> strip_tac >> simp[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> irule expr_val_at_start_mono >> metis_tac[]
QED

Theorem abi_args_word_fits_eq[local]:
  !src dst. arg_type_fits src dst /\ is_word_type dst ==> src = dst
Proof
  Cases >> Cases >>
  simp[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def] >>
  rpt strip_tac >> Cases_on `b` >> Cases_on `b'` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def] >>
  Cases_on `b` >> Cases_on `b''` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def]
QED

Theorem abi_args_local_base_transport[local]:
  local_val_at ce cx n k (BaseTV bt1) v /\
  val_wf (BaseTV bt1) v /\
  val_footprint (BaseTV bt1) v = val_footprint (BaseTV bt2) v ==>
  local_val_at ce cx n k (BaseTV bt2) v
Proof
  simp[local_val_at_def] >> rpt strip_tac >> disj2_tac
  >- (qexists `bt1` >> simp[] >> metis_tac[val_footprint_le]) >>
  qexists `bt0` >> simp[]
QED

Theorem abi_args_rel_lowered_transport:
  expr_body_pre ce cx env e es /\
  expr_val_rel cx (post_value_type ce e) v op s /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v) ==>
  expr_val_rel cx (lowered_value_type ce e) v op s
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  Cases_on `is_word_type (expr_type e)`
  >- (`lowered_value_type ce e = expr_type e` by
        metis_tac[abi_args_word_fits_eq] >>
      gvs[]) >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  first_x_assum drule >> strip_tac >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- gvs[] >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
     IF_CASES_TAC >> simp[]) >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >> qexists `w` >> simp[] >>
  irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >> simp[] >>
  qexistsl [`post_value_type ce e`, `lowered_value_type ce e`, `get_tenv cx`, `ptv`] >>
  simp[]
QED

Theorem abi_args_at_lowered_transport:
  expr_body_pre ce cx env e es /\
  expr_val_at ce cx (post_value_type ce e) sa sb es' v op s /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v) ==>
  expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op s
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  Cases_on `is_word_type (expr_type e)`
  >- (`lowered_value_type ce e = expr_type e` by
        metis_tac[abi_args_word_fits_eq] >> simp[expr_val_at_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- gvs[expr_post_def] >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
     IF_CASES_TAC >> simp[]) >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  `value_has_type ptv v` by
    (Cases_on `post_value_type ce e = lowered_value_type ce e`
     >- gvs[] >>
     `post_value_type ce e = expr_type e` by metis_tac[] >>
     drule (CONJUNCT1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type) >>
     disch_then irule >> metis_tac[]) >>
  `val_footprint ptv v = val_footprint tv v` by
    metis_tac[valueCopyBytesTheory.bytestring_val_footprint_eq] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `val_wf ptv v` by (gvs[expr_val_at_def] >> metis_tac[]) >>
  `!n k. local_val_at ce cx n k ptv v ==> local_val_at ce cx n k tv v` by
    (`?bt1. ptv = BaseTV bt1` by
       metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
     `?bt2. tv = BaseTV bt2` by
       metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
     gvs[] >> metis_tac[abi_args_local_base_transport]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem abi_args_expr_post_lowered_rel:
  expr_body_pre ce cx env e es /\
  expr_post ctx func ce cx e es0 sa sb s0 es' v op s /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v) ==>
  expr_val_rel cx (lowered_value_type ce e) v op s
Proof
  strip_tac >> irule abi_args_rel_lowered_transport >>
  gvs[expr_post_def] >> metis_tac[]
QED

Theorem abi_args_expr_post_lowered_at:
  expr_body_pre ce cx env e es /\
  expr_post ctx func ce cx e es0 sa sb s0 es' v op s /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v) ==>
  expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op s
Proof
  strip_tac >> irule abi_args_at_lowered_transport >>
  gvs[expr_post_def] >> metis_tac[]
QED

Theorem abi_args_post_cons_uncaptured:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (lowered_value_type ce e) ==> es'.scopes = es1.scopes) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >>
  `wb_frame ce es1 es' sm t u` by metis_tac[abi_args_post_def] >>
  `stmt_state_rel ctx func ce cx es1 t` by metis_tac[expr_post_def] >>
  `stmt_state_rel ctx func ce cx es' u` by metis_tac[abi_args_post_def] >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op u` by
    (irule abi_args_location_end_mono >>
     qexists `sm` >> simp[] >> irule abi_args_location_kept >>
     metis_tac[]) >>
  `expr_val_rel cx (lowered_value_type ce e) v op u` by
    (Cases_on `is_word_type (lowered_value_type ce e)`
     >- (qpat_x_assum `expr_val_rel _ _ _ _ t` mp_tac >>
         simp[expr_val_rel_def] >> strip_tac >> qexists `w` >>
         simp[] >> irule abi_args_operand_kept >> metis_tac[]) >>
     `es'.scopes = es1.scopes` by simp[] >>
     `sm.cs_next_id <= sm.cs_next_id` by simp[] >>
     drule_all abi_args_value_kept >> simp[]) >>
  irule abi_args_post_cons_frame >> metis_tac[]
QED

Theorem abi_args_post_cons_uncaptured_labels:
  expr_body_pre ce cx env e es /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v) /\
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (lowered_value_type ce e) ==> es'.scopes = es1.scopes) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  gas_admissible (do r <- eval_expr cx e; read_result cx r od) expr_res_ok es /\
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >> Cases_on `?l. op = Label l`
  >- (gvs[] >>
      `wb_frame ce es1 es' sm t u` by metis_tac[abi_args_post_def] >>
      `stmt_state_rel ctx func ce cx es1 t` by metis_tac[expr_post_def] >>
      `stmt_state_rel ctx func ce cx es' u` by metis_tac[abi_args_post_def] >>
      `expr_val_rel cx (post_value_type ce e) v (Label l) t` by
        metis_tac[expr_post_def] >>
      `expr_val_at ce cx (post_value_type ce e) sa sm es1 v (Label l) t` by
        metis_tac[expr_post_def] >>
      `eval_operand (Label l) t = eval_operand (Label l) u \/
       (expr_val_rel cx (post_value_type ce e) v (Label l) u /\
        expr_val_at ce cx (post_value_type ce e) sa sm es' v (Label l) u)` by
        (irule abi_args_success_label_transport >> metis_tac[ETA_THM]) >>
      pop_assum strip_assume_tac
      >- (`expr_val_at ce cx (lowered_value_type ce e) sa sb es' v (Label l) u` by
            (irule abi_args_location_end_mono >> qexists `sm` >> simp[] >>
             irule abi_args_location_kept_eq >> metis_tac[]) >>
          `expr_val_rel cx (lowered_value_type ce e) v (Label l) u` by
            (Cases_on `is_word_type (lowered_value_type ce e)`
             >- (gvs[expr_val_rel_def] >> metis_tac[]) >>
             `es'.scopes = es1.scopes` by simp[] >>
             `sm.cs_next_id <= sm.cs_next_id` by simp[] >>
             irule abi_args_value_kept_eq >> metis_tac[]) >>
          irule abi_args_post_cons_frame >> metis_tac[]) >>
      `expr_val_rel cx (lowered_value_type ce e) v (Label l) u` by
        (irule abi_args_rel_lowered_transport >> metis_tac[]) >>
      `expr_val_at ce cx (lowered_value_type ce e) sa sm es' v (Label l) u` by
        (irule abi_args_at_lowered_transport >> metis_tac[]) >>
      `expr_val_at ce cx (lowered_value_type ce e) sa sb es' v (Label l) u` by
        metis_tac[abi_args_location_end_mono] >>
      irule abi_args_post_cons_frame >> metis_tac[]) >>
  irule abi_args_post_cons_uncaptured >> metis_tac[]
QED

Theorem abi_args_post_cons_captured:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v /\
  eval_operand op t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es1.scopes t n lb lsz ==>
              b + sz <= lb \/ lb + lsz <= b) ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >>
  `wb_frame ce es1 es' sm t u` by metis_tac[abi_args_post_def] >>
  `stmt_state_rel ctx func ce cx es1 t` by metis_tac[expr_post_def] >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op u` by
    (irule abi_args_location_end_mono >>
     qexists `sm` >> simp[] >> irule abi_args_location_kept >>
     metis_tac[]) >>
  `expr_val_rel cx (lowered_value_type ce e) v op u` by
    (irule abi_args_captured_value_kept >> metis_tac[]) >>
  irule abi_args_post_cons_frame >> metis_tac[]
QED

Theorem abi_args_compile_cons:
  compile_abi_encode_args compile_expr ce (e::args) sa = (ops,sb) <=>
  ?vv mid op sm tail.
    compile_expr ce (expr_type e) e sa = (vv,mid) /\
    (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce args
     then compile_materialize_vv ce (lowered_value_type ce e) vv mid
     else unwrap_value ce vv mid) = (op,sm) /\
    compile_abi_encode_args compile_expr ce args sm = (tail,sb) /\
    ops = op::tail
Proof
  simp[exprLoweringTheory.compile_abi_encode_args_def,
       comp_bind_def, comp_return_def,
       pairTheory.pair_case_thm] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `~is_word_type (expr_type e) /\ exprs_can_mutate ce args` >>
  gvs[] >> metis_tac[]
QED

Theorem abi_args_materialize_not_label:
  compile_materialize_vv ce ty vv sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[exprLoweringTheory.compile_materialize_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[exprSafeOperandTheory.alloc_buffer_not_label]
QED

Theorem abi_args_name_label_forward[local]:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz) /\
  ~is_word_type (expr_type (Name ann id)) ==>
  lower_value compile_expr ce ty (Name ann id) sa = (Label l,sa)
Proof
  simp[exprLoweringTheory.lower_value_def, comp_bind_def,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_expr_body_def,
       exprLoweringTheory.compile_name_vv_def,
       exprLoweringTheory.unwrap_value_def, contextTheory.mk_ptr_def,
       comp_return_def]
QED


Theorem abi_args_operand_live:
  (!x. op = Var x ==> not_fresh_at sm x) /\ ci_mono sm sb ==>
  abi_decoder_operand_live sb.cs_next_var op
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem abi_args_uncaptured_cons_sim_live:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (lowered_value_type ce e) ==> es'.scopes = es1.scopes) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) ops)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops))
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_uncaptured_cons_sim:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (lowered_value_type ce e) ==> es'.scopes = es1.scopes) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s)
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_captured_cons_sim:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (expr_type e) vv mid = (op,sm) /\
  eval_expr cx e es = (INL tvv,es1) /\
  expr_vv_res_ok (INL tvv) /\ read_result cx tvv es1 = (INL v,es1) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\ type_memory_size tv + 64 < dimword (:256) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s)
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_captured_cons_sim_live:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (expr_type e) vv mid = (op,sm) /\
  eval_expr cx e es = (INL tvv,es1) /\
  expr_vv_res_ok (INL tvv) /\ read_result cx tvv es1 = (INL v,es1) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\ type_memory_size tv + 64 < dimword (:256) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) ops)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops))
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_vv_post_read:
  vv_post ctx func ce cx e es sa sb s0 es' tvv vv s ==>
  ?v. read_result cx tvv es' = (INL v,es')
Proof
  Cases_on `vv` >>
  simp[vv_post_def, vv_holds_def] >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

Theorem abi_args_read_vv_res_ok:
  read_result cx tvv es = (res,es') /\ expr_res_ok res ==>
  expr_vv_res_ok (INL tvv)
Proof
  Cases_on `tvv` >>
  simp[expr_vv_res_ok_def, vyperStateTheory.read_result_def,
       expr_res_ok_def] >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem abi_args_exit_inr:
  expr_exit (INR exc : 'a + exception) =
  expr_exit (INR exc : value list + exception)
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac `r` >> Cases_on `exc` >> Cases_on `r` >>
  simp[expr_exit_def] >> rename1 `Error err` >> Cases_on `err` >>
  simp[expr_exit_def]
QED

Theorem abi_args_vv_error_prefix:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  eval_expr cx e es = (INR exc,es') /\
  expr_res_ok (INR exc : value + exception) /\
  fn_has_code sa mid func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cs_extends sa mid /\ cs_extends mid sb ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    Q (wb_args_exit (INR exc))
Proof
  cheat
QED

Theorem abi_args_vv_read_error_prefix:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  eval_expr cx e es = (INL tvv,es') /\
  read_result cx tvv es' = (INR exc,es') /\
  expr_res_ok (INR exc : value + exception) /\
  fn_has_code sa mid func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cs_extends sa mid /\ cs_extends mid sb ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    Q (wb_args_exit (INR exc))
Proof
  cheat
QED

Theorem compile_abi_encode_args_sim_live:
  !args ctx func ce cx Inv env es sa ops sb rr es' s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
      (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops)
      (wb_args_exit rr)
Proof
  cheat
QED

Theorem compile_abi_encode_args_sim:
  !args ctx func ce cx Inv env es sa ops sb rr es' s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
      (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s)
      (wb_args_exit rr)
Proof
  cheat
QED
