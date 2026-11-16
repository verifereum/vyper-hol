(* Source-facing immutable element entry, on the selected array round. *)
Theory bodyFullForArrayImmRoundEntry
Ancestors
  bodyFullForArrayImmStart bodyFullForArrayCtorCopy
  bodyFullForArrayImmScalarCopy bodyFullForArrayImmInstall bodyFullForArrayImmutable
  whitelistForIterImmCopy bodyPtrDefs exprSimCopy
  bodyFullGhostFrame vyperTypeInvariants
  exprSimHypsDefs loweringPosts vyperBareGlobalName vyperState
  vyperValue vyperTyping vyperValueOperation valueEncodingProps
  valueEncodingTyping finite_map list words arithmetic
  fragGasSeqPtr fragGasOriginPtrLoop fragGasEmitCtrl fragExecMem
  fragGasSeqMem memSafeRun instMemFrontier ptrDiscipline
  venomExecSemantics venomInst venomState contextCodegenRel codegenRel
  bodyPtrBopInLiteralSuffix ptrSafeRun fragExec exprLoweringProps

Theorem for_array_immutable_round_observation[local]:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src name = SOME (ArrayTV tv bd,ArrayV av) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  vs = array_elements (ArrayTV tv bd) av /\ k < LENGTH vs ==>
  immutable_holds cenv cx typ (Value (EL k vs))
    (n2w off + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
      k * type_memory_size tv)) es s /\ value_has_type tv (EL k vs)
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv bd) (ArrayV av) /\
   well_formed_type_value (ArrayTV tv bd)` by
    (`state_well_typed es` by fs[expr_sim_inv_def] >>
     gvs[lookup_immutable_def,AllCaseEqs()] >>
     `MEM (cx.txn.target,imms) es.immutables` by metis_tac[alistTheory.ALOOKUP_MEM] >>
     fs[state_well_typed_def,EVERY_MEM] >>
     first_x_assum drule >> simp[] >>
     simp[imms_well_typed_def] >> strip_tac >>
     Cases_on `ALOOKUP imms src` >>
     gvs[get_source_immutables_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tv bd)` by
    (fs[expr_sim_inv_def,env_consistent_def,env_immutables_consistent_def] >>
     gvs[lookup_immutable_def,AllCaseEqs()] >> metis_tac[]) >>
  `src = cenv.ce_module /\
   off + type_memory_size (ArrayTV tv bd) < dimword (:256)` by
    (fs[expr_sim_inv_def] >>
     qpat_x_assum `!src id ty. _` drule >> strip_tac >> gvs[]) >>
  gvs[lookup_immutable_def,AllCaseEqs()] >>
  `immutable_holds cenv cx (ArrayT typ bd) (Value (ArrayV av))
    (n2w off) es s` by
    (simp[immutable_holds_def,read_result_def,return_def] >>
     qexistsl_tac [`name`,`off`,`ArrayTV tv bd`,`ArrayV av`,`0`] >>
     simp[sub_layout_def]) >>
  `val_wf (ArrayTV tv bd) (ArrayV av)` by
    metis_tac[value_has_type_val_wf] >>
  drule immutable_iter_element_ready >>
  simp[read_result_def,return_def] >>
  disch_then (qspec_then `k` mp_tac) >> simp[]
QED

(* Nonempty immutable entry takes the body branch.  The condition is a
   scalar step: its chosen ghosts are independent of the horizon. *)
Theorem for_array_immutable_nonempty_condition[local]:
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx;bound_op] [dv];
       mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|> /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var idx s = SOME (n2w k) /\
  eval_operand bound_op s = SOME (n2w len) /\
  k < len /\ len < dimword (:256) /\
  FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
  op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ?G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to body_lbl (update_var dv 0w s)),G1,tn1)) /\
    (!x. x <> dv ==> FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm
Proof
  strip_tac >>
  `n2w k <> (n2w len : 256 word)` by
    (simp[wordsTheory.n2w_11] >> decide_tac) >>
  qabbrev_tac `i = mk_inst j1 EQ [Var idx;bound_op] [dv]` >>
  qabbrev_tac `u = update_var dv 0w s` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i] s G1 tn1` by
    (gen_tac >>
     `step_inst_base i s = OK u` by
       simp[Abbr `i`,Abbr `u`,step_inst_base_opcode_eqs,mk_inst_def,
         exec_pure2_def,eval_operand_def,bool_to_word_def] >>
     `ptr_inst_ok D lo 0 ctx func G tn i s` by
       (simp[Abbr `i`,ptr_inst_ok_def,access_ok_def,taint_ok_def,
          mk_inst_def,source_memory_write_ranges_def,source_memory_read_ranges_def] >>
        simp[GSYM mk_inst_def,step_inst_non_invoke] >>
        simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
          eval_operand_def,update_var_def,allocas_from_def,op_prov_def] >>
        simp[Abbr `u`,update_var_def] >>
        conj_tac >- (rpt strip_tac >> gvs[op_prov_def,FLOOKUP_DEF]) >>
        gen_tac >> Cases_on `op = Var idx` >> simp[] >>
        Cases_on `op = bound_op` >> simp[]) >>
     simp[inst_seq_ptr_def,Abbr `G1`,Abbr `tn1`]) >>
  `(!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (jump_to body_lbl u),G1,tn1))` by
    (gen_tac >>
     `run_inst_seq [i] s = OK u` by
       simp[run_inst_seq_def,Abbr `i`,Abbr `u`,step_inst_base_opcode_eqs,
         mk_inst_def,eval_operand_def,exec_pure2_def,bool_to_word_def] >>
     `run_inst_seq_mem_ok [i] s` by
       (irule run_inst_seq_mem_ok_every >>
        simp[Abbr `i`,mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK (u with vs_inst_idx := 1),G1,tn1)` by
       (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
        simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
        disch_then irule >> conj_tac
        >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
        gvs[mk_inst_def]) >>
     `op_taint tn1 (Var dv) = {}` by
       simp[Abbr `tn1`,Abbr `i`,Abbr `u`,step_taint_def,op_taint_def,
         set_var_taint_def,out_taint_def,mk_inst_def,eval_operand_def,FLOOKUP_UPDATE] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u with vs_inst_idx := 1,G1,tn1) []
        (OK (jump_to body_lbl (u with vs_inst_idx := 1)),G1,tn1)` by
       (irule (jnz_origin_ptr_path |> Q.INST
          [`w` |-> `0w`, `l1` |-> `exit_lbl`, `l2` |-> `body_lbl`]
          |> SIMP_RULE (srw_ss()) []) >>
        simp[Abbr `u`,update_var_def,eval_operand_def,lookup_var_def,
          FLOOKUP_UPDATE,allocas_from_def] >>
        qexistsl_tac [`Var dv`,`exit_lbl`,`j2`] >>
        gvs[Abbr `i`,get_instruction_def,update_var_def,eval_operand_def,
          lookup_var_def,FLOOKUP_UPDATE]) >>
     drule_all gas_origin_ptr_path_trans >> simp[jump_to_def]) >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`,Abbr `i`,Abbr `u`,membership_scalar_ghost_frame] >>
  qexistsl_tac [`G1`,`tn1`] >> simp[] >>
  simp[Abbr `G1`,Abbr `i`,step_prov_def,out_prov_def,
    set_prov_def,FLOOKUP_DRESTRICT,op_taint_def,mk_inst_def,FLOOKUP_UPDATE]
QED

Theorem for_array_address_taint[local]:
  MEM opc [ADD;MUL] /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst j opc [a;b] [x]) s u tn =
    tn with t_var := tn.t_var |+ (x,{})
Proof
  strip_tac >> gvs[MEM]
  >- (irule stmtAppendStorageRunPtrTheory.scalar_add_taint >> simp[]) >>
  irule (cj 2 typedCopyLoopHeaderPtrTheory.typed_copy_loop_arith_ghost_clean) >>
  simp[] >> metis_tac[]
QED

(* Literal immutable element addressing, including the dynamic length header. *)
Theorem for_array_immutable_address_sequence[local]:
  lookup_var idx s = SOME (n2w k) /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  code = [mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]] ++
    (case bd of Fixed n => []
     | Dynamic n => [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
    [mk_inst j4 ADD [Lit (n2w off);
      (case bd of Fixed n => Var ov | Dynamic n => Var tov)] [ep]] ==>
  ?z Gf tf.
    run_inst_seq code s = OK z /\
    lookup_var ep z = SOME
      (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes)) /\
    (!D n. inst_seq_ptr D lo ctx func PG G tn code
      (s with vs_inst_idx := n) Gf tf) /\
    (z with vs_vars := s.vs_vars) = s /\
    (!x. x <> ov /\ x <> tov /\ x <> ep ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    op_prov Gf (Var ep) = NONE /\ op_taint tf (Var ep) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >> Cases_on `bd` >> gvs[]
  >- (qexistsl_tac
        [`update_var ep (n2w off + n2w k * n2w bytes)
           (update_var ov (n2w k * n2w bytes) s)`,
         `DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {ep})`,
         `tn with t_var := tn.t_var |+ (ov,{}) |+ (ep,{})`] >>
      simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
        eval_operand_def,exec_pure2_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE,
        word_mul_n2w,word_add_n2w] >>
      conj_tac
      >- (rpt gen_tac >>
          simp[inst_seq_ptr_def,step_inst_base_opcode_eqs,mk_inst_def,
            eval_operand_def,exec_pure2_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
          rpt conj_tac >>
          simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,
            mk_inst_def,source_memory_write_ranges_def,source_memory_read_ranges_def,
            step_inst_non_invoke,op_taint_def,op_prov_def,allocas_from_def,
            step_prov_def,out_prov_def,set_prov_def,first_prov_def,
            step_taint_def,out_taint_def,set_var_taint_def,update_var_def,
            new_site_bytes_def,mem_taint_def,step_writes_def,store_taint_def,
            written_taint_def,adopt_reset_def,imm_taint_def,range_bytes_def,
            step_inst_base_opcode_eqs,eval_operand_def,exec_pure2_def,
            lookup_var_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] >>
          gvs[op_taint_def,allocas_from_def]
          >- (rpt strip_tac >> gvs[])
          >- (conj_tac
              >- (gen_tac >> Cases_on `op = Lit (n2w off)` >> simp[] >>
                  Cases_on `op = Var ov` >> simp[]) >> metis_tac[]) >>
          simp[FLOOKUP_DEF,SF CONJ_ss,taint_component_equality]) >>
      simp[op_taint_def,op_prov_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
      rpt strip_tac >> simp[]) >>
  qexistsl_tac
    [`update_var ep (n2w off + (32w + n2w k * n2w bytes))
       (update_var tov (32w + n2w k * n2w bytes)
         (update_var ov (n2w k * n2w bytes) s))`,
     `DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {tov})) (COMPL {ep})`,
     `tn with t_var := tn.t_var |+ (ov,{}) |+ (tov,{}) |+ (ep,{})`] >>
  conj_tac
  >- simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
       eval_operand_def,exec_pure2_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
      pure_rewrite_tac[word_mul_n2w,word_add_n2w] >>
      simp[AC ADD_ASSOC ADD_COMM,AC MULT_ASSOC MULT_COMM]) >>
  conj_tac
  >- (rpt gen_tac >>
      simp[inst_seq_ptr_def,step_inst_base_opcode_eqs,mk_inst_def,
        eval_operand_def,exec_pure2_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
      rpt conj_tac >>
      simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,
        mk_inst_def,source_memory_write_ranges_def,source_memory_read_ranges_def,
        step_inst_non_invoke] >>
      simp[step_prov_def,out_prov_def,set_prov_def,first_prov_def,
        mk_inst_def,FLOOKUP_DRESTRICT,op_prov_def] >>
      simp[step_inst_base_opcode_eqs,eval_operand_def,exec_pure2_def,
        lookup_var_def,update_var_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,
        op_taint_def,allocas_from_def] >>
      pure_rewrite_tac[GSYM mk_inst_def] >>
      simp[for_array_address_taint,op_taint_def,FLOOKUP_UPDATE] >>
      gvs[op_taint_def,allocas_from_def]
      >- (rpt strip_tac >> gvs[])
      >- (conj_tac
          >- (gen_tac >> Cases_on `op = Lit 32w` >> simp[] >>
              Cases_on `op = Var ov` >> simp[]) >> metis_tac[])
      >- (conj_tac
          >- (gen_tac >> Cases_on `op = Lit (n2w off)` >> simp[] >>
              Cases_on `op = Var tov` >> simp[]) >> metis_tac[]) >>
      simp[FLOOKUP_DEF,SF CONJ_ss,taint_component_equality,pred_setTheory.INTER_ASSOC]) >>
  simp[update_var_def,lookup_var_def,op_taint_def,op_prov_def,
    FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem for_array_immutable_round_entry_full:
  body_inv tops ctx cenv cx /\
  supported_stmts tops bindings stmts /\
  aty = ArrayT typ bd /\
  id NOTIN FDOM env.var_types /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  saved_base = Lit (n2w off) /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  declare_local cenv id typ sdecl = (bc,sdecl') /\ same_frame cenv bc /\
  cenv_top_ext cenv bc (FEMPTY :: ee.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id ee.scopes = NONE /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved bc scopy /\
  ret_pc_ok cenv sa s0 /\ copy_old_operand scopy bound_op /\
  ~ctx_has_dalloca ctx /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> idx /\ x <> dv /\ x <> ov /\ x <> ep) /\
  not_fresh_at scopy idx /\ not_fresh_at scopy p /\ not_fresh_at scopy ep /\
  p <> ov /\ p <> ep /\
  not_local_ptr cenv ee.scopes ov /\ not_local_ptr cenv ee.scopes ep /\
  ALL_DISTINCT [idx;dv;ov;ep;p] /\
  (bd = Dynamic (bound_length bd) ==> ALL_DISTINCT [idx;dv;ov;tov;ep;p]) /\
  (!x. bound_op = Var x ==> x <> dv /\ x <> ov /\ x <> tov /\
    x <> ep /\ x <> idx /\ x <> nv) /\
  (!x. saved_base = Var x ==> x <> dv /\ x <> ov /\ x <> tov /\ x <> ep) /\
  (!region x. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
    x <> idx /\ x <> dv /\ x <> ov /\ x <> tov /\ x <> ep /\ x <> nv) /\
  fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx;bound_op] [dv];
       mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|> /\
  lookup_block body_lbl func.fn_blocks = SOME
    <|bb_label := body_lbl; bb_instructions := sb0.cs_current_insts ++ tail_code|> /\
  scopy.cs_current_bb = body_lbl /\
  scopy.cs_current_insts =
    [mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]] ++
    (case bd of Fixed n => []
     | Dynamic n => [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
    [mk_inst j4 ADD [Lit (n2w off);
      (case bd of Fixed n => Var ov | Dynamic n => Var tov)] [ep]] /\
  not_fresh_at scopy tov /\ tov <> p /\ tov <> idx /\
  (!x. not_fresh_at sa x ==> x <> tov) /\
  (joff <> j3 /\ joff <> j4) /\
  compile_iter_elem_copy cenv (Var ep) (Var p) bytes LocCode F typ typ
    scopy = ((),sb0) /\ fn_has_code scopy sb0 func /\
  cs_extends scopy sb0 /\ scopy.cs_next_var <= sb0.cs_next_var /\
  bytes = type_memory_size tv /\ type_memory_bytes cenv typ = bytes /\
  0 < bytes /\ bytes + 64 < dimword (:256) /\
  extent = (if bytes <= 32 then 32 else 32*((bytes+31) DIV 32)) /\
  sz = type_memory_bytes cenv typ /\ extent <= sz /\
  sa.cs_next_var <= scopy.cs_next_var /\
  sa.cs_next_var <= sb0.cs_next_var /\ cs_extends sa sb0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  k < LENGTH vs /\ MAP Value (DROP k vs) = Value v :: rs /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    dead_lo_ok H (DF H) lo cenv cx /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    LENGTH vs < dimword (:256) /\ lookup_var idx s = SOME (n2w k) /\
    eval_operand bound_op s = SOME (n2w (LENGTH vs)) /\
    FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
    op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
    lookup_immutable cx ee src name = SOME (ArrayTV tv bd,ArrayV av) /\
    vs = array_elements (ArrayTV tv bd) av /\
    (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
      eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
      op_prov G region = NONE /\ copy_old_operand scopy region) /\
    lookup_var p s = SOME dst /\ ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= s.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes s nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) ==>
  ?ss Gs ts. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK ss,Gs,ts) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) /\
    stmt_state_rel H ctx func bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) ss /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d bc sb0 ss /\ alloca_history func ss /\
    ghost_inv_at (DF H) lo d bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) Gs ts ss /\
    ~ss.vs_halted /\ ss.vs_current_bb = sb0.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ret_pc_ok bc sb0 ss /\
    allocas_from lo ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
    lookup_var p ss = SOME dst /\ ptr_covers Gs ts p ss sz /\
    FLOOKUP ss.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= ss.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes ss nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    lookup_var idx ss = SOME (n2w k) /\
    eval_operand bound_op ss = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gs idx = NONE /\ op_prov Gs bound_op = NONE /\
    op_taint ts (Var idx) = {} /\ op_taint ts bound_op = {} /\
    lookup_immutable cx ee src name = SOME (ArrayTV tv bd,ArrayV av) /\
    vs = array_elements (ArrayTV tv bd) av /\
    (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
      eval_operand region ss = SOME 0w /\ op_taint ts region = {} /\
      op_prov Gs region = NONE /\ copy_old_operand scopy region /\
      copy_old_operand sb0 region) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x ss = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP ss.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gs x = FLOOKUP G0 x /\
      op_taint ts (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (mk_asm "head") >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by
    (qexists_tac `storage_trace_horizon ee.storage_trace` >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  asm "head" (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  `v = EL k vs` by
    (qpat_x_assum `MAP Value (DROP k vs) = _` mp_tac >>
     simp[MAP_EQ_CONS] >> rpt strip_tac >>
     `HD (DROP k vs) = EL k vs` by simp[HD_DROP] >> gvs[]) >>
  drule_all for_array_immutable_nonempty_condition >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qabbrev_tac `u = jump_to body_lbl (update_var dv 0w s)` >>
  `lookup_var idx u = SOME (n2w k) /\
   FLOOKUP G1 idx = NONE /\ op_taint tn1 (Var idx) = {} /\
   allocas_from lo u` by
    (gvs[ALL_DISTINCT,Abbr `u`,jump_to_def,update_var_def,
      lookup_var_def,FLOOKUP_UPDATE,allocas_from_def] >> metis_tac[]) >>
  drule_all for_array_immutable_address_sequence >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `x <> dv /\ x <> ov /\ x <> tov /\ x <> ep` by metis_tac[] >>
     `lookup_var x u = lookup_var x s` by
       simp[Abbr `u`,jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `not_local_ptr cenv ee.scopes dv` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sa` >>
     metis_tac[]) >>
  `z = u with vs_vars := z.vs_vars` by
    (qpat_assum `z with vs_vars := u.vs_vars = u`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `!HH. valid_horizon cx st0 HH ee.storage_trace ==>
    stmt_state_rel HH ctx func cenv cx ee z` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel HH ctx func cenv cx ee u` by
       (simp[Abbr `u`,stmt_state_rel_jump_to] >>
        irule stmt_state_rel_update_var >> asm "head" (qspec_then `HH` mp_tac) >> simp[]) >>
     qpat_assum `z = u with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >> rename1 `lookup_var old _ = _` >>
     `not_fresh_at sa old` by
       metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     `lookup_var old z = lookup_var old s` by metis_tac[] >>
     `old <> dv` by metis_tac[] >>
     gvs[lookup_var_def,Abbr `u`,jump_to_def,update_var_def,FLOOKUP_UPDATE]) >>
  `immutable_holds cenv cx typ (Value v)
    (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes)) ee z /\
   value_has_type tv v` by
    (drule_all for_array_immutable_round_observation >>
     disch_then (qspec_then `z` mp_tac) >>
     simp[word_add_n2w,AC ADD_ASSOC ADD_COMM]) >>
  `type_memory_size tv = 32 /\
   (cenv.ce_is_ctor ==>
     w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*32):bytes32)+32 <= lo /\
     mem_word_taint tn.t_mem
       (w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*32):bytes32)) = {})` by
    (drule_all for_array_immutable_element_resources_full >> simp[]) >>
  `z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next /\ z.vs_fmp = s.vs_fmp /\
   z.vs_current_bb = body_lbl /\ z.vs_inst_idx = 0 /\ ~z.vs_halted` by
    (qpat_assum `z = u with vs_vars := z.vs_vars`
       (fn th => once_rewrite_tac [th]) >>
     simp[Abbr `u`,jump_to_def,update_var_def]) >>
  `lookup_var p z = SOME dst /\ ptr_covers Gf tf p z 32 /\
   allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (simp[allocas_from_def,ptr_covers_def] >>
     gvs[ptr_covers_def,ALL_DISTINCT,Abbr `u`,jump_to_def,update_var_def,
       lookup_var_def,FLOOKUP_UPDATE,allocas_from_def,ghost_inv_at_def] >>
     rpt strip_tac >>
     qpat_x_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> lo <= b` drule >>
     simp[]) >>
  `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    copy_old_operand scopy region /\ eval_operand region z = SOME 0w /\
    op_taint tf region = {} /\ op_prov Gf region = NONE` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==> _`
       (qspec_then `region` mp_tac) >> simp[] >> strip_tac >>
     namedCases_on `region` ["w","rr","lab"]
     >- (qpat_x_assum `eval_operand (Lit w) s = SOME 0w` mp_tac >>
         simp[eval_operand_def,op_taint_def,op_prov_def,copy_old_operand_def])
     >- (`rr <> dv /\ rr <> ov /\ rr <> tov /\ rr <> ep` by
           (qpat_x_assum `!region x. _ /\ _ /\ region = Var x ==> _`
              (qspecl_then [`Var rr`,`rr`] mp_tac) >> simp[]) >>
         `lookup_var rr z = lookup_var rr s /\ FLOOKUP Gf rr = FLOOKUP G rr /\
          op_taint tf (Var rr) = op_taint tn (Var rr)` by
           (`lookup_var rr u = lookup_var rr s` by
              simp[Abbr `u`,jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
            metis_tac[]) >>
         qpat_x_assum `eval_operand (Var rr) s = SOME 0w` mp_tac >>
         qpat_x_assum `op_prov G (Var rr) = NONE` mp_tac >>
         simp[eval_operand_def,op_prov_def]) >>
     qpat_x_assum `eval_operand (Label lab) s = SOME 0w` mp_tac >>
     simp[eval_operand_def,op_taint_def,op_prov_def,copy_old_operand_def] >>
     qpat_assum `z = u with vs_vars := z.vs_vars`
       (fn th => once_rewrite_tac[th]) >>
     simp[Abbr `u`,jump_to_def,update_var_def]) >>
  `copy_old_operand scopy (Var ep) /\ copy_old_operand scopy (Var p)` by
    simp[copy_old_operand_def] >>
  `compile_iter_elem_copy cenv (Var ep) (Var p) 32 LocCode F typ typ scopy = ((),sb0)` by
    metis_tac[] >>
  `eval_operand (Var ep) z = SOME
     (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes))` by
    simp[eval_operand_def] >>
  `(cenv.ce_is_ctor ==>
    w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes):bytes32)+32 <= lo /\
    mem_word_taint tf.t_mem
      (w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes):bytes32)) = {} /\
    (!region. cenv.ce_imm_alloca = SOME region ==>
      copy_old_operand scopy region /\ eval_operand region z = SOME 0w /\
      op_taint tf region = {} /\ op_prov Gf region = NONE))` by
    (qpat_x_assum `cenv.ce_is_ctor ==> _ /\ mem_word_taint tn.t_mem _ = {}` mp_tac >>
     simp[]) >>
  drule_all for_array_immutable_scalar_copy_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by metis_tac[] >>
  `eval_operand (Var p) z = SOME dst` by simp[eval_operand_def] >>
  `lo <= w2n dst` by
    (qpat_x_assum `ptr_covers Gf tf p z 32` mp_tac >>
     qpat_x_assum `allocas_from lo z` mp_tac >>
     simp[ptr_covers_def,allocas_from_def] >> metis_tac[]) >>
  `(cenv.ce_is_ctor ==> regions_disjoint
    (w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes):bytes32))
    bytes (w2n dst) bytes)` by
    (strip_tac >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_x_assum `cenv.ce_is_ctor ==> _ /\ mem_word_taint tf.t_mem _ = {} /\ _`
       mp_tac >> simp[]) >>
  `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region z = SOME 0w /\ copy_old_operand scopy region` by metis_tac[] >>
  `bytes = 32 /\ sz = 32 /\ extent = 32 /\
   w2n dst + 32 < dimword (:256)` by gvs[] >>
  `32 = type_memory_size tv` by simp[] >>
  `(cenv.ce_is_ctor ==> regions_disjoint
    (w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*bytes):bytes32))
    32 (w2n dst) 32)` by metis_tac[] >>
  `0 < (32:num)` by decide_tac >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  `z'' = z'` by
    (qpat_x_assum `copy_runtime_frame scopy z sb0 z''`
       (mp_tac o cj 1 o REWRITE_RULE [copy_runtime_frame_def]) >>
     qpat_x_assum `copy_runtime_frame scopy z sb0 z'`
       (mp_tac o cj 1 o REWRITE_RULE [copy_runtime_frame_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_x_assum `z'' = z'` SUBST_ALL_TAC >>
  qabbrev_tac `empty = ee with scopes := FEMPTY :: ee.scopes` >>
  qabbrev_tac `pushed = ee with <|scopes :=
    (FEMPTY |+ (id,<|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
    gas_obs := []|>` >>
  `expr_sim_inv bc cx (extend_local env id typ F) pushed` by
    (drule_all bodyExprPreFactsTheory.expr_sim_inv_for_scope >>
     strip_tac >>
     qpat_x_assum `expr_sim_inv bc _ _ _`
       (mp_tac o Q.INST [`gs` |-> `[]`] o MATCH_MP (iffRL expr_sim_inv_gas_obs)) >>
     simp[Abbr `pushed`, Excl "expr_sim_inv_gas_obs"]) >>
  `bc.ce_module_vars = cenv.ce_module_vars /\ bc.ce_module = cenv.ce_module /\
   bc.ce_is_ctor = cenv.ce_is_ctor /\ bc.ce_imm_alloca = cenv.ce_imm_alloca /\
   bc.ce_module_var_type = cenv.ce_module_var_type` by
    (qpat_x_assum `cenv_top_ext cenv bc _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[cenv_top_ext_def,compileEnvTheory.compile_env_component_equality] >>
     strip_tac >> gvs[]) >>
  `!HH. valid_horizon cx st0 HH ee.storage_trace ==>
    stmt_state_rel HH ctx func bc cx empty z` by
    (gen_tac >> strip_tac >> irule stmt_state_rel_cenv_cong >>
     qexists_tac `cenv` >> simp[Abbr `empty`,stmt_state_rel_push_scope] >>
     rpt strip_tac >>
     irule forPtrScopeTheory.cenv_top_ext_outer_lookup >>
     qexistsl_tac [`e`,`ee.scopes`,`FEMPTY`] >>
     fs[lookup_scopes_def]) >>
  `not_local_ptr bc empty.scopes p` by
    (qpat_assum `local_ptrs_reserved bc scopy` mp_tac >>
     qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz)` mp_tac >>
     qpat_assum `lookup_scopes id ee.scopes = NONE` mp_tac >>
     qunabbrev_tac `empty` >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringStateRelDefsTheory.not_local_ptr_def,
       loweringStateRelDefsTheory.local_ptrs_reserved_def,lookup_scopes_def] >>
     rpt strip_tac >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `!q. q = p \/ ~not_local_ptr bc empty.scopes q ==> not_fresh_at scopy q` by
    (qpat_assum `local_ptrs_reserved bc scopy` mp_tac >>
     qpat_assum `not_fresh_at scopy p` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringStateRelDefsTheory.not_local_ptr_def,
       loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `!HH. valid_horizon cx st0 HH ee.storage_trace ==>
    stmt_state_rel HH ctx func bc cx pushed z'` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel HH ctx func bc cx empty z` by metis_tac[] >>
     `stmt_state_rel HH ctx func bc cx
       (empty with scopes := (FEMPTY |+ (id,
         <|assignable := F; type := tv; value := v; popped := []|>))::ee.scopes) z'`
       suffices_by
       (disch_then (mp_tac o Q.INST [`gs` |-> `[]`] o
          MATCH_MP (iffRL exprSimWordArgsTheory.stmt_state_rel_gas_obs)) >>
        simp[Abbr `empty`,Abbr `pushed`,Excl "stmt_state_rel_gas_obs"]) >>
     irule stmtSimForArrayTheory.array_iter_copy_declare_rel >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- simp[Abbr `empty`]) >>
     (conj_tac >- simp[Abbr `empty`,lookup_scopes_def]) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     qexistsl_tac [`ainst`,`p`,`z`,`scopy`,`sz`,`dst`] >>
     (conj_tac >- (qpat_assum `type_memory_size tv = 32` (fn th => rewrite_tac [th]) >>
       qpat_assum `sz = 32` (fn th => rewrite_tac [th]) >> decide_tac)) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- (qpat_assum `copy_runtime_frame scopy z sb0 z'` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[copy_runtime_frame_def])) >>
     (conj_tac >- (qpat_assum `type_memory_size tv = 32` (fn th => rewrite_tac [th]) >>
       first_assum MATCH_ACCEPT_TAC)) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
     (conj_tac >- (qpat_assum `FLOOKUP s.vs_allocas ainst.inst_id = _` mp_tac >>
       qpat_assum `z.vs_allocas = s.vs_allocas` mp_tac >>
       qpat_assum `sz = 32` mp_tac >>
       qpat_assum `type_memory_size tv = 32` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[])) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> not_fresh_at scopy x` by
    (qpat_assum `sa.cs_next_var <= scopy.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z' = lookup_var x s /\ FLOOKUP Gf' x = FLOOKUP G x /\
    op_taint tf' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at scopy x` by metis_tac[] >>
     `lookup_var x z' = lookup_var x z` by
       metis_tac[copy_runtime_frame_def] >> metis_tac[]) >>
  `!a len. a+len <= w2n dst \/ w2n dst+32 <= a ==>
    mem_bytes_at a len z'.vs_memory = mem_bytes_at a len s.vs_memory` by
    metis_tac[] >>
  `!j. j < w2n dst \/ w2n dst+32 <= j ==>
    (j IN tf'.t_mem <=> j IN tn.t_mem)` by
    (simp[] >> rpt strip_tac >> decide_tac) >>
  `!i. w2n dst <= i /\ i < w2n dst+32 ==> i NOTIN tf'.t_mem` by simp[] >>
  `z'.vs_allocas = s.vs_allocas /\ z'.vs_alloca_next = s.vs_alloca_next /\
   ~z'.vs_halted /\ allocas_from lo z' /\ lo <= z'.vs_alloca_next` by
    (`z'.vs_allocas = z.vs_allocas /\ z'.vs_alloca_next = z.vs_alloca_next /\
      z'.vs_halted = z.vs_halted` by
       metis_tac[copy_runtime_frame_def,exprSimStorageCopyTheory.copy_static_fields] >>
     fs[allocas_from_def]) >>
  `lookup_var p z' = SOME dst /\ ptr_covers Gf' tf' p z' sz` by
    (conj_tac >- metis_tac[copy_runtime_frame_def] >>
     qpat_assum `sz = 32` (fn th => rewrite_tac[th]) >>
     irule immutableCopySeqPtrTheory.ptr_covers_copy_runtime_frame >>
     qexistsl_tac [`Gf`,`z`,`scopy`,`sb0`,`tf`] >> simp[]) >>
  FAIL_TAC "entry-exterior"
QED
