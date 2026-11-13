(* Read-only captured word argument unwrap. *)
Theory extcallUnwrapWordMemory
Ancestors
  exprSimMemUnwrap exprSimUnwrap exprSimConvert bodyMemBiLenPath
  exprSimBopRestWordLoadSafety exprSimBopRestWordLayout
  exprSimBopRestWordLoadPath loweringPosts fragGasPathMem
  exprLowering compileEnv valueEncodingProps venomState words list

Theorem captured_word_load_run[local]:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location
    p.ptr_operand sm = (op,su) /\
  p.ptr_location <> LocCalldata /\ eval_operand p.ptr_operand s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\
  vv_holds cenv cx lt (Value v) (LocatedValue lt p) es s /\
  read_result cx (Value v) es = (INL v,es) /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\ is_word_type lt /\
  (p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w) ==>
  ?q. run_inst_seq (emitted_insts sm su) s = OK q /\
    eval_operand op q = SOME (typed_val_to_w256 ltv v)
Proof
  strip_tac >>
  drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >>
  simp[] >> disch_then (qspecl_then [`s`, `w`] mp_tac) >> simp[] >>
  `((case p.ptr_location of
     LocStorage => sload w s | LocTransient => tload w s |
     LocCode => if cenv.ce_is_ctor then mload (w2n w) s else
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) |
     _ => mload (w2n w) s) = typed_val_to_w256 ltv v)` by
    (Cases_on `p.ptr_location` >>
     gvs[vv_holds_def, GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]
     >~ [`storage_holds cx F lt (Value v) w es s`]
       >- (drule_all storage_holds_load >> simp[])
     >~ [`storage_holds cx T lt (Value v) w es s`]
       >- (drule_all storage_holds_load >> simp[]) >>
     Cases_on `cenv.ce_is_ctor` >> gvs[]
     >- (drule_all immutable_holds_iload >>
         simp[valueEncodingPropsTheory.mem_word_at_eq_mload])
     >> drule_all immutable_holds_dload >> simp[]) >>
  gvs[] >> Cases_on `cenv.ce_is_ctor` >>
  Cases_on `cenv.ce_imm_alloca` >> gvs[WORD_ADD_0]
QED

Theorem captured_word_load_bounds[local]:
  stmt_state_rel ctx func cenv cx es s /\
  vv_holds cenv cx lt (Value v) (LocatedValue lt p) es s /\
  eval_operand p.ptr_operand s = SOME w /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\ type_memory_size ltv = 32 /\
  (p.ptr_location = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) /\
  (p.ptr_location = LocCode /\ cenv.ce_is_ctor ==>
    !region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) ==>
  ((p.ptr_location = LocMemory \/ (p.ptr_location = LocCode /\ cenv.ce_is_ctor)) ==>
    w2n w + 32 <= s.vs_alloca_next) /\
  (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor ==>
    w2n w <= LENGTH s.vs_data_section) /\
  (p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)
Proof
  strip_tac >> Cases_on `p.ptr_location` >> gvs[] >>
  `immutable_holds cenv cx lt (Value v) w es s` by gvs[vv_holds_def] >>
  drule_all rest_word_immutable_region_bound >>
  Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[] >> rpt strip_tac >> decide_tac
QED

Theorem extcall_captured_unwrap_word_mem:
  unwrap_value cenv vv sm = (op,su) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  read_result cx (Value v) es = (INL v,es) /\
  vv_holds cenv cx t (Value v) vv es s /\
  vv_store_bound cx t lt es (Value v) vv s /\
  vv_storage_live cx vv es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\ val_wf tv v /\
  type_memory_bytes cenv lt = type_memory_size ltv /\
  type_memory_size ltv < dimword (:256) /\
  (!ty src. vv = StackValue ty src ==>
    !x. src = Var x ==> not_fresh_at sm x) /\
  (!ty p. vv = LocatedValue ty p ==> ty = lt /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (p.ptr_location <> LocMemory ==> t = lt) /\
    (is_word_type lt /\ p.ptr_location = LocMemory ==>
      !w. eval_operand p.ptr_operand s = SOME w ==>
        w2n w + 32 <= s.vs_alloca_next) /\
    (p.ptr_location = LocCode /\ cenv.ce_is_ctor ==>
      !region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))) /\
  (?p. vv = LocatedValue lt p /\ is_word_type lt) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\ ~z.vs_halted /\
    z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    expr_val_rel cx t v op z /\ expr_store_bound cx t v op z /\
    (!w. ~is_word_type t /\ eval_operand op z = SOME w ==>
      type_memory_size ltv = 0 \/
      w2n w + type_memory_size ltv <= z.vs_alloca_next) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    (!off len. off + len <= s.vs_alloca_next ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ alloca_history func z /\
    stmt_state_rel ctx func cenv cx es z /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels
Proof
  strip_tac >> gvs[unwrap_value_def] >>
  `t = lt` by
    (gvs[vv_holds_def] >> metis_tac[is_word_type_not_bytestring]) >>
  gvs[] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> gvs[vv_holds_def]) >>
  `?w. eval_operand p.ptr_operand s = SOME w` by
    gvs[vv_holds_def] >>
  `type_memory_size ltv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `((p.ptr_location = LocMemory \/
       (p.ptr_location = LocCode /\ cenv.ce_is_ctor)) ==>
       w2n w + 32 <= s.vs_alloca_next) /\
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor ==>
       w2n w <= LENGTH s.vs_data_section) /\
   (p.ptr_location = LocCode /\ cenv.ce_is_ctor /\
       cenv.ce_imm_alloca <> NONE ==>
       eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (irule captured_word_load_bounds >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm su) s` by
    (drule_all rest_word_ptr_load_mem_ok >> simp[]) >>
  `?q. run_inst_seq (emitted_insts sm su) s = OK q /\
       eval_operand op q = SOME (typed_val_to_w256 ltv v)` by
    (drule_all captured_word_load_run >> simp[]) >>
  `alloca_inv s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule_all len_ptr_load_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (drule rest_word_ptr_load_fresh >>
     gvs[EVERY_MEM, lookup_var_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := u.vs_vars)` by
    (irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >>
     qmatch_goalsub_rename_tac `lookup_var nm (s with vs_vars := _)` >>
     `not_fresh_at sm nm` by (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     fs[lookup_var_def]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     `stmt_state_rel ctx func cenv cx es
       ((s with vs_vars := u.vs_vars) with vs_inst_idx := LENGTH su.cs_current_insts)`
       suffices_by simp[] >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
  qexists `u` >>
  gvs[expr_val_rel_def, expr_val_at_def, exprSimMemDefsTheory.expr_store_bound_def,
      contract_storage_def, contract_transient_def] >>
  qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
  simp[]
QED
