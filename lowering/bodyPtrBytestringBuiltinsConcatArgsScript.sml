(* Pointer-safe traversal of Concat operands. *)
Theory bodyPtrBytestringBuiltinsConcatArgs
Ancestors
  bodyPtrBytestringBuiltinsConcatHead bodyPtrBytestringBuiltinsEval
  bodyPtrPreds bodyPtrDefs bodySim exprSimConcatArgs exprSimHypsDefs
  bodyPtrEnvBuiltinsGhostCompose
  exprSimSource exprSimProps exprSimDefs exprLowering exprLoweringProps compileEnv loweringStateRelDefs
  loweringPosts fragExec fragGasPathPtr gasSummaryComposePtr gasOutcomeMapPtr
  assignTuplePtrBodyReady stmtFragPtr logGhostFramePtr wordArgsPtr exprSimWordArgs vyperInterpreter vyperState vyperValue
  vyperTypeInvariants vyperTypeExprSoundness venomState words arithmetic finite_map list rich_list
Libs
  monadsyntax

Theorem concat_child_suffix_mono:
  compile_concat compile_expr cenv (e::args) dp ((is_bs,m)::infos) off sa = ((),sb) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,s1) ==>
  ci_mono s1 sb
Proof
  strip_tac >>
  qpat_x_assum `compile_concat _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_concat_def] >> Cases_on `is_bs` >>
  simp[Once comp_bind_def] >>
  qmatch_goalsub_abbrev_tac `stp s1 = ((),sb) ==> _` >>
  `ci_mono s1 (SND (stp s1))` suffices_by (rpt strip_tac >> gvs[]) >>
  qunabbrev_tac `stp` >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
    (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE gen_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_concat_cfn,
       cj 1 compile_expr_ci_mono]
QED

Theorem concat_args_sim_ptr:
  !args P k ctx func cenv cx env es sa sb s0 dv ov ow binst B bsz oinst G0 tn0 PG tops d.
  compile_concat compile_expr cenv args (Var dv)
    (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
      else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m) | _ => (F,32:num)) args)
    (Var ov) sa = ((),sb) /\
  EVERY (\e. is_bytestring_type (expr_type e) \/ ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
  expr_sim_inv cenv cx env es /\
  (!e st. MEM e args /\ expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) /\
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dv s0 = SOME (n2w (B+32)) /\ lookup_var ov s0 = SOME ow /\
  not_fresh_at sa dv /\ not_fresh_at sa ov /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  binst.inst_id < sa.cs_next_id /\ FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  oinst.inst_id < sa.cs_next_id /\ FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\ B+bsz < dimword (:256) /\
  mload (w2n ow) s0 = n2w k /\ k <= P /\
  32+P+SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
  32+concat_data_bound P (MAP expr_type args) <= bsz /\
  ghost_inv d cenv cx es G0 tn0 s0 /\
  ptr_covers G0 tn0 dv s0 (bsz-32) /\ ptr_covers G0 tn0 ov s0 32 /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn0.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn0.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_exprs cx args) (es,s0,G0,tn0)
    (\rr ee G tn t. ?vs. rr = INL vs /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee t /\
      LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) args vs /\
      mem_bytes_at (B+32) (k+LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs))) t.vs_memory =
        mem_bytes_at (B+32) k s0.vs_memory ++ FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs) /\
      mload (w2n ow) t = n2w (k+LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs))) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
        (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
        (!name lo sz. local_region cenv es.scopes s0 name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept cenv es s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
      ptr_covers G tn dv t (bsz-32) /\ ptr_covers G tn ov t 32 /\ ~t.vs_halted /\
      (!i. B+32 <= i /\ i < B+32+k+LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs)) ==> i NOTIN tn.t_mem) /\
      (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem))
    (\rr ee gt r. ?exc. rr = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      gvs[compile_concat_def, comp_return_def] >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL []`,`es`,`G0`,`tn0`,`OK s0`] >>
      simp[eval_exprs_nil, gas_path_ptr_rules, locals_kept_refl, ghost_kept_refl,
           ghost_inv_gas_obs]) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rename1 `body_exprs_ptr_ok cx (e::args)` >>
  `expr_body_pre cenv cx env e es` by
    (qpat_x_assum `!e st. _ ==> _` (qspecl_then [`e`,`es`] mp_tac) >> simp[]) >>
  qpat_x_assum `body_exprs_ptr_ok _ (_::_)`
    (strip_assume_tac o REWRITE_RULE [body_exprs_ptr_ok_def]) >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    (fs[Once body_expr_ptr_ok_def] >> metis_tac[]) >>
  qpat_assum `EVERY _ (_::_)`
    (CONJUNCTS_THEN assume_tac o BETA_RULE o REWRITE_RULE [EVERY_DEF]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ _ sa = (op,s1)` >>
  `ci_mono sa s1` by (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono s1 sb` by
    (Cases_on `is_bytestring_type (expr_type e)`
     >- (qpat_assum `is_bytestring_type (expr_type e)` (fn th =>
           qpat_assum `compile_concat _ _ (_::_) _ _ _ _ = _`
             (assume_tac o SIMP_RULE (srw_ss()) [th])) >>
         drule_all concat_child_suffix_mono >> simp[]) >>
     `?m. expr_type e = BaseT (BytesT (Fixed m))` by metis_tac[] >>
     qpat_assum `expr_type e = BaseT (BytesT (Fixed m))` (fn th =>
       qpat_assum `compile_concat _ _ (_::_) _ _ _ _ = _`
         (assume_tac o SIMP_RULE (srw_ss()) [th, is_bytestring_type_def])) >>
     drule_all concat_child_suffix_mono >> simp[]) >>
  `fn_has_code sa s1 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule expr_sim_ptr_eval_suffix >>
  simp[] >>
  first_assum (irule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac >- simp[oneline expr_exit_def] >> suspend "head"
QED

Resume concat_args_sim_ptr[head]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?marks ee0. _` strip_assume_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all expr_body_pre_eval_gas_ptr >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `expr_sim_inv cenv cx env es` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (qpat_x_assum `value_runtime_typed env (expr_type e) v` mp_tac >>
     qpat_x_assum `env.type_defs = get_tenv cx` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[value_runtime_typed_def]) >>
  `body_exprs_ptr_ok cx args` by
    (qpat_x_assum `bind _ _ _ = (INL v,ee)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all concat_head_arm_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "tail"
QED

Resume concat_args_sim_ptr[tail]:
  irule gas_outcome_ptr_prefix >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  irule gasOutcomeMapPtrTheory.gas_outcome_ptr_map_return >>
  qpat_assum `!P k ctx func cenv cx env es sa sb s0 dv ov ow binst B bsz oinst G0 tn0 PG tops d. _`
    (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  qpat_assum `compile_concat _ _ args _ _ _ s2 = _`
    (irule_at (Pat `compile_concat _ _ _ _ _ _ _ = _`)) >>
  qpat_assum `ghost_inv d cenv cx ee Gf tnf t2`
    (irule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  qpat_assum `mload (w2n ow) t2 = _`
    (irule_at (Pat `mload _ _ = _`)) >>
  qexistsl [`tops`, `oinst`, `env`, `bsz`, `binst`,
            `P + concat_payload_capacity (expr_type e)`, `B`] >>
  qpat_x_assum `!P k ctx func cenv cx env es sa sb s0 dv ov ow binst B bsz oinst G0 tn0 PG tops d. _`
    kall_tac >>
  simp[] >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (qpat_x_assum `ci_mono sa s1` mp_tac >>
     qpat_x_assum `ci_mono s1 s2` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ci_mono_def]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac >- (qpat_x_assum `!name lb lsz. local_region cenv ee.scopes t2 _ _ _ ==> _` mp_tac >>
               simp[]) >>
  conj_tac >- (qpat_x_assum `32 + P + SUM _ <= bsz` mp_tac >> simp[]) >>
  conj_tac >- (qpat_x_assum `32 + concat_data_bound P _ <= bsz` mp_tac >>
               rpt (pop_assum kall_tac) >>
               simp[concat_data_bound_def] >>
               Cases_on `is_bytestring_type (expr_type e)` >> simp[MAX_ALT]) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  suspend "compose"
QED

Resume concat_args_sim_ptr[compose]:
  conj_tac >- (rpt gen_tac >> strip_tac >>
              qpat_x_assum `res = INL vs` SUBST1_TAC >>
              qexists_tac `v::vs` >> simp[] >>
              qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
                (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
              conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
              conj_tac >- metis_tac[] >>
              suspend "frames") >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `res = INR exc` SUBST1_TAC >> simp[]
QED

Resume concat_args_sim_ptr[frames]:
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t2 = SOME w` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t2.vs_allocas aid = SOME a` by
    metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es s0` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `!n b sz. local_region cenv ee.scopes t2 n b sz <=>
             local_region cenv es.scopes s0 n b sz` by
    (qpat_assum `local_ptrs_rel func cenv es.scopes s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP FDOM es.scopes = MAP FDOM ee.scopes` mp_tac >>
     qpat_assum `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t2 = SOME w` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> eq_tac
     >- metis_tac[local_region_frame] >>
     metis_tac[local_region_frame_fwd]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    `mem_bytes_at p n t'.vs_memory = mem_bytes_at p n t2.vs_memory` by
      (qpat_x_assum `!aid p n. _ ==> mem_bytes_at p n t'.vs_memory = mem_bytes_at p n t2.vs_memory` irule >>
       simp[] >> conj_tac
       >- (qpat_assum `!n b sz. local_region cenv ee.scopes t2 n b sz <=> _` mp_tac >>
           qpat_assum `ee = ee0 with gas_obs := []` mp_tac >>
           qpat_assum `!name lo sz. local_region cenv es.scopes s0 name lo sz ==> _` mp_tac >>
           rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
       qexists_tac `aid` >> conj_tac
       >- (qpat_assum `ci_mono sa s1` mp_tac >>
           qpat_assum `ci_mono s1 s2` mp_tac >> simp[ci_mono_def]) >>
       metis_tac[]) >>
    `mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory` by
      (qpat_assum `!p n. _ ==> mem_bytes_at p n t2.vs_memory = _` irule >>
       simp[ADD_SYM]) >>
    `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory` by
      (qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz t.vs_memory = _`
         (qspecl_then [`aid`,`p`,`n`] mp_tac) >> simp[ADD_SYM] >>
       impl_tac >- metis_tac[ADD_SYM] >> simp[]) >>
    simp[]) >>
  suspend "locals_ghost"
QED

Resume concat_args_sim_ptr[locals_ghost]:
  conj_tac
  >- (`locals_kept cenv es s0 t2` by
        (irule locals_kept_regions_tail >>
         qpat_assum `locals_kept cenv es s0 t` (irule_at (Pat `locals_kept _ _ _ _`)) >>
         rpt strip_tac >>
         qpat_assum `!p n. _ ==> mem_bytes_at p n t2.vs_memory = _` irule >>
         metis_tac[]) >>
      irule exprBopSimPropsTheory.locals_kept_trans >>
      qpat_assum `locals_kept cenv es s0 t2` (irule_at (Pat `locals_kept _ _ _ _`)) >>
      qpat_assum `locals_kept cenv _ t2 t'` (irule_at (Pat `locals_kept _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_locals_trans >>
     qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G tn`
       (irule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
     qpat_assum `ghost_kept cenv ee s1 G tn t Gf tnf`
       (irule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def]) >>
  irule ghost_kept_frame_trans >>
  qpat_assum `ghost_kept cenv es sa G0 tn0 s0 Gf tnf`
    (irule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  qpat_assum `ghost_kept cenv _ s2 Gf tnf t2 G' tn'`
    (irule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  simp[] >> conj_tac
  >- (qpat_assum `!n b sz. local_region cenv ee.scopes t2 n b sz <=> _` mp_tac >>
      qpat_assum `ee = ee0 with gas_obs := []` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Finalise concat_args_sim_ptr
