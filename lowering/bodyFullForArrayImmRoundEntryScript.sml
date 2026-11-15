(* Source-facing immutable element entry, on the selected array round. *)
Theory bodyFullForArrayImmRoundEntry
Ancestors
  bodyFullForArrayImmStart bodyFullForArrayCtorCopy
  whitelistForIterImmCopy
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
