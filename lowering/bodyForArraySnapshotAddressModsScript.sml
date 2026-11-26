(* Byte-addressed array loops skip a length word only on dynamic arrays. *)
Theory bodyForArraySnapshotAddressMods
Ancestors
  bodyFullSubscriptArrayCodeOps decoderOriginAllocationFrame gasOriginPtrLabels
  loweringShapeRules loweringShapeDefs stmtSimProps emitHelper compileEnv
  fragGasOriginPtr fragGasOriginPtrLoop fragExec exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState venomInst context vyperAST
  words finite_map pred_set arithmetic

Theorem snapshot_alloca_scalar[local]:
  u.vs_allocas = s.vs_allocas /\ u.vs_initial_fmp = s.vs_initial_fmp /\
  u.vs_fmp = s.vs_fmp ==>
  (allocas_from lo u <=> allocas_from lo s) /\
  (allocas_below_fmp u <=> allocas_below_fmp s)
Proof
  strip_tac >> asm_rewrite_tac[allocas_from_def,allocas_below_fmp_def]
QED

Theorem for_array_snapshot_address_mods:
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (off_op,sm) /\
  (case bd of Fixed _ => sum_op = off_op /\ sn = sm
    | Dynamic _ => emit_op ADD [Lit 32w;off_op] sm = (sum_op,sn)) /\
  emit_op ADD [base_op;sum_op] sn = (addr,saCopy) /\ fn_has_code sa saCopy func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\ (!lbl. base_op <> Label lbl) /\
  eval_operand base_op s = SOME bw /\ op_taint tn base_op = {} /\
  lookup_var idx s = SOME (n2w k) /\ op_taint tn (Var idx) = {} /\ FLOOKUP G idx = NONE /\
  allocas_from lo s /\ fn_inst_ids_distinct func ==>
  ?out u Gu tu.
    addr = Var out /\ not_fresh_at saCopy out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    u.vs_current_bb = saCopy.cs_current_bb /\ u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\
    ~u.vs_halted /\
    lookup_var out u = SOME (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + k*stride)) /\
    op_taint tu addr = {} /\ op_prov Gu addr = op_prov G base_op /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_immutables = s.vs_immutables /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_data_section = s.vs_data_section /\ u.vs_fmp = s.vs_fmp /\
    u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_requests = s.vs_requests /\ u.vs_labels = s.vs_labels /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q u = lookup_var q s /\ FLOOKUP Gu q = FLOOKUP G q /\
      op_taint tu (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es u)
Proof
  strip_tac >>
  `eval_operand (Var idx) s = SOME (n2w k) /\ op_prov G (Var idx) = NONE` by
    simp[eval_operand_def,op_prov_def] >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  rename1 `off_op = Var off` >>
  qpat_assum `emit_op ADD [base_op;sum_op] _ = _`
    (mp_then Any strip_assume_tac emit_op_facts) >>
  rename1 `addr = Var out` >>
  Cases_on `bd` >> gvs[]
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume for_array_snapshot_address_mods[fixed]:
  drule_all scalar_mul_add_joint_frame >> disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gu`,`tu`,`u`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by simp[] >>
  pop_assum (qspec_then `ARB` assume_tac) >>
  drule_then assume_tac gas_origin_ptr_path_preserves_labels >>
  drule_all_then strip_assume_tac decoder_origin_path_allocation_frame >>
  drule_all_then (qspec_then `lo` strip_assume_tac) snapshot_alloca_scalar >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[]
QED

Resume for_array_snapshot_address_mods[dynamic]:
  qpat_assum `emit_op ADD [Lit 32w;Var off] _ = _`
    (mp_then Any strip_assume_tac emit_op_facts) >>
  rename1 `sum_op = Var sum` >> gvs[] >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn saCopy` by
    metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  `fn_has_code sa sn func /\ fn_has_code sn saCopy func` by
    metis_tac[ci_mono_def,cs_extends_trans,fn_has_code_split] >>
  `(!x. Lit 32w = Var x ==> not_fresh_at sa x) /\ (!l. Lit 32w <> Label l) /\
   eval_operand (Lit 32w) s = SOME 32w /\ op_taint tn (Lit 32w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  drule_all (scalar_mul_add_joint_frame |> Q.INST [`base_op` |-> `Lit 32w`]) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac) >>
  `gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s1,G1,tn1)` by simp[] >>
  drule_all_then strip_assume_tac decoder_origin_path_allocation_frame >>
  `op_prov G1 (Var sum) = NONE` by simp[op_prov_def] >>
  `eval_operand base_op s1 = SOME bw /\ op_taint tn1 base_op = {} /\
   op_prov G1 base_op = op_prov G base_op` by
    (Cases_on `base_op` >> gvs[eval_operand_def,op_taint_def,op_prov_def]) >>
  `eval_operand (Var sum) s1 = SOME (32w + n2w (k * stride))` by simp[eval_operand_def] >>
  drule_all_then (qspec_then `lo` strip_assume_tac) snapshot_alloca_scalar >>
  `allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by simp[] >>
  drule_all (scalar_binop_joint_frame |> Q.INST
    [`opc` |-> `ADD`, `w` |-> `a + b : bytes32`] |> SRULE []) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s2,G2,tn2)` by
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s1,G1,tn1)` by simp[] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) [] (OK s2,G2,tn2)` by simp[] >>
     drule_all_then ACCEPT_TAC gas_origin_ptr_path_trans) >>
  pop_assum (fn th => assume_tac th >> assume_tac (Q.SPEC `ARB` th)) >>
  drule_then assume_tac gas_origin_ptr_path_preserves_labels >>
  qpat_assum `s2.vs_allocas = s1.vs_allocas` (mp_then Any (drule_all_then (qspec_then `lo` strip_assume_tac)) snapshot_alloca_scalar) >>
  qexistsl_tac [`s2`,`G2`,`tn2`] >> simp[word_add_n2w] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn q` by metis_tac[ci_mono_def,not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv sn` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Finalise for_array_snapshot_address_mods
