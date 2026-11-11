(* Seam 2 joint induction step: the forced-value producer from the value producer. *)
Theory bodyIntCallJointForce
Ancestors
  bodyIntCallJointContract bodyIntCallWindowForcing bodyIntCallAssembly exprBopSimProps
  exprLoweringProps exprSimProps freshWrites stmtSimProps bodyMemoryDefs
  loweringPosts exprOperandVar exprSimUnwrap exprSimMemorySource fragExec
  gasOutcome gasSummaryCompose exprSimHyps exprSimHypsDefs abiBuiltinEncodeWord exprSimBopRestWordBasics

Theorem unwrap_value_operand_reserved:
  unwrap_value ce vv sa = (op,sb) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  strip_tac >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `vv` |-> `vv`,
    `sa` |-> `sa`, `op` |-> `op`, `sb` |-> `sb`] compiler_unwrap_value_var) >>
  Cases_on `vv` >> gvs[contextTheory.vv_operand_def]
QED

(* Compose the joint entry frame with an old-window-preserving suffix. *)
Theorem intcall_expr_cont_suffix:
  intcall_expr_cont fp ce env es sa s ee sm t /\
  expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sa /\
  fp.jc_reserved fp.jc_rpc /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  allocas_above fp.jc_lo u /\ t.vs_alloca_next <= u.vs_alloca_next /\
  (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k t.vs_memory) /\
  (!q. fp.jc_reserved q ==> eval_operand q u = eval_operand q t) /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
     lookup_var x u = SOME w) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
     aid < sa.cs_next_id /\
     (!n b len. local_region ce es.scopes s n b len ==>
       off + sz <= b \/ b + len <= off) ==>
     mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory) /\
  locals_kept ce ee ee t u /\
  (!name b sz. local_region ce ee.scopes u name b sz <=>
     local_region ce ee.scopes t name b sz) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `!n b sz. local_region ce es.scopes s n b sz ==>
     local_region ce ee.scopes t n b sz` by
    (rpt strip_tac >> irule expr_inv_local_regions_transport >>
     fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
     goal_assum (drule_at Any) >>
     qexistsl [`fp.jc_cx`, `env`, `sa`] >> simp[]) >>
  fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
  rpt conj_tac >> simp[]
  >- metis_tac[local_ptrs_reserved_next_var]
  >- metis_tac[freshWritesTheory.not_fresh_at_mono]
  >- metis_tac[]
  >- (irule ret_pc_ok_frame >> goal_assum (drule_at Any) >> qexists `ce` >> simp[])
  >- (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> qexists `ce` >> simp[])
  >- metis_tac[]
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >> irule locals_kept_trans >>
  qpat_assum `local_ptrs_reserved ce sa` (irule_at Any) >>
  qpat_assum `locals_kept ce ee ee t u` (irule_at Any) >> metis_tac[]
QED

Theorem intcall_joint_window_forcing:
  intcall_frame_ok fp /\
  intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s ee sm t /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  unwrap_value ce vv sm = (op,sb) /\
  vv_holds ce fp.jc_cx ty r vv ee t /\
  read_result fp.jc_cx r ee = (INL v,ee) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) t = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\
     a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    expr_val_rel fp.jc_cx ty v op u /\
    (!sv. sv.cs_next_id <= sm.cs_next_id /\ vv_at ce fp.jc_cx ty sv sm ee r vv t ==>
       expr_val_at ce fp.jc_cx ty sv sb ee v op u) /\
    (!sv. sv.cs_next_id <= sm.cs_next_id /\ vv_own ce fp.jc_cx ty sv sm ee r vv t ==>
       expr_val_own ce fp.jc_cx ty sv sb ee v op u) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
       ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
         w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
         (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
    intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[unwrap_value_operand_reserved] >>
  `sm.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sm`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  qabbrev_tac `Win = \off sz. ?aid. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\
    (!n b len. local_region ce es.scopes s n b len ==> off+sz <= b \/ b+len <= off)` >>
  `!p k. Win p k ==> ?aid b len. aid < sm.cs_next_id /\
     FLOOKUP t.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len` by
    (rw[Abbr `Win`] >> qexistsl [`aid`, `p`, `k`] >>
     fs[intcall_expr_cont_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `t`, `es` |-> `ee`,
    `P` |-> `fp.jc_prot`, `lo` |-> `fp.jc_lo`,
    `staged` |-> `fp.jc_staged`, `reserved` |-> `fp.jc_reserved`,
    `Win` |-> `Win`, `scopes` |-> `ee.scopes`,
    `ctx` |-> `fp.jc_ctx`, `cx` |-> `fp.jc_cx`,
    `func` |-> `fp.jc_func`] protected_value_window_forcing) >>
  (impl_tac >-
    (qpat_assum `intcall_expr_cont _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def]) >>
     qpat_assum `intcall_frame_ok _`
       (strip_assume_tac o REWRITE_RULE [intcall_frame_ok_def]) >> simp[])) >>
  strip_tac >> qexists `u` >>
  simp[] >>
  irule intcall_expr_cont_suffix >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `intcall_expr_res _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_joint_res_def, intcall_expr_res_def]) >>
  qpat_x_assum `intcall_frame_ok _`
    (strip_assume_tac o REWRITE_RULE [intcall_frame_ok_def]) >>
  simp[] >> qexistsl [`sm`, `t`] >> simp[Abbr `Win`] >>
  metis_tac[]
QED

Theorem arg_type_fits_memory_bytes:
  (!sty dty. arg_type_fits sty dty ==>
     type_memory_bytes ce sty <= type_memory_bytes ce dty) /\
  (!stys dtys. arg_types_fit stys dtys ==>
     SUM (MAP (type_memory_bytes ce) stys) <=
     SUM (MAP (type_memory_bytes ce) dtys))
Proof
  ho_match_mp_tac vyperTypeSystemTheory.arg_type_fits_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[vyperTypeSystemTheory.arg_type_fits_def,
       compileEnvTheory.type_memory_bytes_def] >>
  rpt strip_tac >> gvs[]
  >- (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[])
  >- (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[])
  >- (irule arithmeticTheory.LESS_MONO_MULT2 >> simp[]) >>
  metis_tac[]
QED

Theorem type_alloc_ok_memory_bound:
  type_alloc_ok ce ty ==> type_memory_bytes ce ty < 2**64
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (drule abi_builtin_encode_word_info >> simp[]) >>
  fs[allocLimitsTheory.type_alloc_ok_def]
QED

Theorem intcall_force_post_memory_bound:
  expr_body_pre ce cx env e es ==>
  type_memory_bytes ce (post_value_type ce e) < 2**64
Proof
  strip_tac >>
  `type_memory_bytes ce (expr_type e) < 2**64` by
    (irule type_alloc_ok_memory_bound >>
     irule alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_def]) >>
  `type_widens_to env.type_defs (post_value_type ce e) (expr_type e)` by
    (irule post_value_type_widens >>
     conj_tac >- fs[expr_body_pre_def] >>
     qexistsl [`cx`, `es`] >> fs[expr_body_pre_def]) >>
  fs[vyperTypeSystemTheory.type_widens_to_def] >>
  drule (cj 1 arg_type_fits_memory_bytes) >>
  disch_then (qspec_then `ce` assume_tac) >> decide_tac
QED

Theorem intcall_force_static_layout:
  expr_body_pre ce cx env e es ==>
  ?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
       type_memory_bytes ce (post_value_type ce e) = type_memory_size tv /\
       type_memory_size tv < 2**64
Proof
  strip_tac >> drule post_type_evaluates >> strip_tac >>
  drule intcall_force_post_memory_bound >> strip_tac >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size tv` suffices_by
    (strip_tac >> qexists `tv` >> gvs[]) >>
  irule expr_sim_inv_memory_size >>
  goal_assum (drule_at Any) >> qexistsl [`env`, `es`] >>
  fs[expr_body_pre_def]
QED

Theorem gas_marked_exec_bind_zero_suffix:
  gas_marked_exec memory (ctx,func) source (es,s) marks (INL x) mid (OK t) /\
  gas_marked_path memory ctx func t 0 r /\
  (!tail. next x ((mid with gas_obs := []) with gas_obs := tail) =
          (res,fin with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx,func) (bind source next) (es,s) marks res fin r
Proof
  strip_tac >>
  `gas_marked_exec memory (ctx,func) (next x)
     (mid with gas_obs := [],t) [] res fin r` by
    simp[gasSummaryTheory.gas_marked_exec_def, gasSummaryTheory.gas_explicit_def] >>
  drule_all gas_marked_exec_bind_normal >> simp[]
QED

(* L-force: the forced-value sibling of any expression from its value
   producer, by protected_value_forcing at the value's endpoint. *)
Theorem intcall_forced_producer_from_value:
  intcall_expr_producer fp e ==> intcall_forced_producer fp e
Proof
  rewrite_tac[intcall_expr_producer_def, intcall_forced_producer_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr ce ty e sa` >> rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  `unwrap_value ce vv sm = (op,sb)` by
    fs[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def] >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule forced_expr_admissible_raw >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` DISJ_CASES_TAC) >> qexists `marks`
  >- (disj1_tac >>
      (rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
      (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (qx_choose_then `res` (qx_choose_then `es_end` (qx_choose_then `r` strip_assume_tac)) o
         REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]))
      >- (gvs[] >>
          drule intcall_force_static_layout >> strip_tac >>
          drule rest_word_vv_read_suffix >> strip_tac >>
          `read_result fp.jc_cx tv (es_end with gas_obs := []) =
             (INL v,es_end with gas_obs := [])` by
            (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`) intcall_joint_window_forcing >>
          disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
          disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
          disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
          disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
          (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
          disch_then (qx_choose_then `u_force` strip_assume_tac) >>
          qexistsl [`INL v`, `es_end with gas_obs := []`, `OK u_force`] >>
          conj_tac
          >- (irule gas_marked_exec_bind_zero_suffix >>
              goal_assum (drule_at Any) >>
              qexistsl [`es_end`, `tv`] >> simp[]) >>
          simp[] >> rpt conj_tac >>
          metis_tac[arithmeticTheory.ADD_COMM])) >>
      (Cases_on `res` >> gvs[] >>
       rename1 `expr_exit (INR exc) r` >>
       qexistsl [`INR exc`, `es_end`, `r`] >>
       conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
       simp[] >> metis_tac[expr_exit_INR_type])) >>
  disj2_tac >>
  qpat_x_assum `?err ee leaf finish. _` (qx_choose_then `err` (qx_choose_then `ee`
    (qx_choose_then `leaf` (qx_choose_then `finstate` assume_tac)))) >>
  drule force_exempt_cert >>
  disch_then (qspec_then `fp.jc_cx` assume_tac) >>
  qexistsl [`err`, `ee`, `leaf`, `finstate`] >> simp[]
QED
