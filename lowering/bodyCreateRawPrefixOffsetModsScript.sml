(* The copied bytecode keeps its registered owner; ADD only derives a cursor. *)
Theory bodyCreateRawPrefixOffsetMods
Ancestors
  bodyAbiTupleBufferStateMods bodyFullSubscriptArrayCodeOps
  bodyPtrMakeArrayEmission bodyForRangeScalarFrameMods bodyFullUnwrapRun
  assignBasePtrOffset appendStorageGhostPtr bodyMemoryDefs exprSimWordArgs
  allocaHistory exprLoweringProps loweringShapeRules emitHelperProps freshWrites
  bodyPtrDefs fragGasOriginPtr gasOriginPtrLabels loweringPosts compileEnv context emitHelper
  venomState venomInst ptrDiscipline finite_map pred_set words memoryReadProps

Theorem raw_create_prefix_offset_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase cap root root 0 [] b v Gv tv /\
  read_memory pbase (LENGTH bs) v = bs /\
  (!i. pbase <= i /\ i < pbase + LENGTH bs ==> i NOTIN tv.t_mem) /\
  LENGTH bs <= cap /\ pbase + cap < dimword (:256) /\
  FLOOKUP Gv root = SOME (pbase,cap) /\
  (!x. len = Var x ==> not_fresh_at b x) /\
  eval_operand len v = SOME (n2w (LENGTH bs)) /\
  op_taint tv len = {} /\ op_prov Gv len = NONE /\
  local_ptrs_reserved ce se /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at se x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at se x) /\
  allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
  emit_op ADD [Var root;len] b = (op,c) /\ fn_has_code b c func ==>
  ?dst z Gz tz. op = Var dst /\ ci_mono b c /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase cap root dst (LENGTH bs) bs c z Gz tz /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\
    op_taint tz len = {} /\ op_prov Gz len = NONE /\
    FLOOKUP Gz root = SOME (pbase,cap) /\ FLOOKUP Gz dst = SOME (pbase,cap) /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!x. not_fresh_at b x ==> lookup_var x z = lookup_var x v /\
      FLOOKUP Gz x = FLOOKUP Gv x /\ op_taint tz (Var x) = op_taint tv (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (v,Gv,tv) [] (OK z,Gz,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `op_taint tv (Var root) = {} /\ lookup_var root v = SOME (n2w pbase)` by
    (conj_tac
     >- (qpat_assum `ptr_covers Gv tv root v cap`
           (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >> first_assum ACCEPT_TAC) >>
     fs[eval_operand_def]) >>
  drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  rename1 `op = Var dst` >> qpat_x_assum `op = Var dst` SUBST_ALL_TAC >>
  drule_all (scalar_binop_joint_frame |> INST_TYPE [``:'a`` |-> ``:256``] |> Q.INST
    [`opc` |-> `ADD`, `w` |-> `a + b : bytes32`] |> SRULE []) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gz`,`tz`,`z`] strip_assume_tac) >>
  `ci_mono b c` by metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `b.cs_next_var <= c.cs_next_var /\ shared < c.cs_next_id /\
   se.cs_next_var <= c.cs_next_var` by decide_tac >>
  `!x. not_fresh_at se x ==> not_fresh_at b x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved ce b` by metis_tac[local_ptrs_reserved_next_var] >>
  qexistsl [`dst`,`z`,`Gz`,`tz`] >>
  conj_tac >- simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "buffer" >>
  `z.vs_labels = v.vs_labels` by
    (`gas_origin_ptr_path (ARB,lo,ARB,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)` by simp[] >>
     drule_then ACCEPT_TAC gas_origin_ptr_path_preserves_labels) >>
  `eval_operand len z = eval_operand len v /\ op_taint tz len = op_taint tv len /\
   op_prov Gz len = op_prov Gv len` by
    (Cases_on `len` >> fs[eval_operand_def,op_taint_def,op_prov_def]) >>
  `FLOOKUP Gz root = FLOOKUP Gv root` by simp[] >>
  `FLOOKUP Gz dst = SOME (pbase,cap)` by
    (qpat_assum `op_prov Gz (Var dst) = _`
       (assume_tac o SRULE [op_prov_def]) >> fs[]) >>
  `(allocas_from lo z <=> allocas_from lo v) /\
   (allocas_below_fmp z <=> allocas_below_fmp v)` by
    (pure_rewrite_tac[allocas_from_def,allocas_below_fmp_def] >> simp[]) >>
  simp[]
QED

Resume raw_create_prefix_offset_mods[buffer]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ immutable_frame_mods func ce cx ee z` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     conj_tac
     >- (first_assum match_mp_tac >> simp[]) >>
     simp[] >> conj_tac
     >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`Gv`,`ee`,`v`,`se`,`tv`] >>
         simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
     irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`v`,`se`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  `return_buf_frame d ce c z` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`v`,`b`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  `wb_frame ce ee ee se s z` by
    (irule wb_frame_readonly_tail >> qexistsl [`b`,`v`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s Gz tz` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`Gv`,`tv`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  `alloca_history func z` by suspend "history" >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    (conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     simp[fresh_output_props]) >>
  `ptr_covers Gz tz root z cap` by
    (irule ptr_covers_old_transport >> qexistsl [`Gv`,`v`,`b`,`tv`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  `ptr_covers Gz tz dst z (cap - LENGTH bs)` by suspend "coverage" >>
  suspend "assemble"
QED

Resume raw_create_prefix_offset_mods[history]:
  qpat_x_assum `alloca_history func v` mp_tac >>
  simp[alloca_history_def] >> strip_tac >> rpt strip_tac >> gvs[] >>
  `k < v.vs_inst_idx \/ k = v.vs_inst_idx` by decide_tac
  >- (first_x_assum irule >> simp[] >> qexists `k` >> fs[]) >>
  gvs[mk_inst_def]
QED

Resume raw_create_prefix_offset_mods[coverage]:
  `pbase < dimword (:256) /\ pbase + LENGTH bs < dimword (:256)` by decide_tac >>
  irule assign_base_ptr_covers_offset_address >>
  qpat_assum `ptr_covers Gv tv root v cap` (irule_at Any) >>
  qexistsl [`n2w pbase`,`LENGTH bs`,`cap`,`pbase`] >>
  fs[op_prov_def, w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

Resume raw_create_prefix_offset_mods[assemble]:
  `eval_operand (Var root) z = SOME (n2w pbase)` by simp[eval_operand_def] >>
  `read_memory pbase (LENGTH bs) z = bs` by
    (qpat_assum `read_memory pbase (LENGTH bs) v = bs`
       (assume_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
     simp[read_memory_eq_mem_bytes_at]) >>
  simp[abi_tuple_buffer_state_mods_def,eval_operand_def,word_add_n2w] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise raw_create_prefix_offset_mods
