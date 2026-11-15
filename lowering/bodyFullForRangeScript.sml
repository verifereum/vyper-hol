(* Same-selected-run range scaffolding.  The sequence-pointer premises of
   these internal boundaries are discharged by the range assembly, not by
   an additional premise of compile_for_frag_full.  In particular Gf/tf
   are fixed before the horizon: inst_seq_ptr's ghost is determined by
   the concrete prefix, independently of the dead mask. *)
Theory bodyFullForRange
Ancestors
  stmtForRangeChecksMemory stmtForRangeMemoryParts fragGasOriginPtrLoop
  fragGasSeqPtr fragGasSeqMem fragExecMem instMemFrontier
  venomExecSemantics venomExecProofs venomInst venomState
  ptrDiscipline list rich_list words fragExec exprLoweringProps memSafeRun
  fragGasEmitCtrl bodyPtrPrecompileBuiltinsSuffix gasEvents gasCount
  exprPtrUnwrapCopyEdges emitHelperProps fragGasOriginPtr vyperStorageFootprint
  stmtLowering compileEnv context emitHelper ptrSafeRun codegenRel contextCodegenRel
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST
  bodyFullForRounds stmtSimForParts stmtSimForRange gasOutcomeFullCompose
  gasStorage exprSimSource vyperTypeInvariants vyperValue vyperStorageTrace
  stmtLoweringMono bodyFullAllocaFresh bodyPtrDefs forPtrCheckedScalar
  forPtrCheckedEntryGhost
  ghostPcTransportPtr bodyFullForRangeSlot bodyFullForRangeScalar
  gasShadowStmtEnv bodyFullForRangeInit bodyFullForRangeEmpty
  bodyFullForRangeStart bodyFullForRangeBody bodyFullForRangeSuffix
    gasOutcomeFullGuarded bodyExprPreFacts supportedStmtTraverse vyperTypeCallGraph
  vyperTypeCallStackSoundness supportedExprTraverse exprSimHyps allocLimitsProps
  gasShadowCompileStmtHelpers gasShadowCompileStmtOps gasExemptCert vyperTypeValues

val _ = Parse.hide "body";

(* Declaration consumes the pointer register before emitting its ALLOCA.
   The combined compiler action is the canonical buffer allocation at s2. *)
Theorem for_range_local_alloc_buffer_eq:
  cenv.ce_alloca_locals /\
  declare_local cenv id fty s2 = (bc,sd) /\
  emit_local_alloca bc id sd = ((),sa) ==>
  compile_alloc_buffer (type_memory_bytes cenv fty) s2 =
    (<|buf_operand := Var (STRING #"%" (toString s2.cs_next_var));
       buf_size := type_memory_bytes cenv fty|>,sa)
Proof
  simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
       LET_THM] >> strip_tac >> gvs[] >>
  gvs[emit_local_alloca_def, finite_mapTheory.FLOOKUP_UPDATE,
      emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, compile_alloc_buffer_def,
      emit_op_def, fresh_var_def]
QED

Theorem for_range_literal_entry_path_full:
  code = [mk_inst i1 ASSIGN [Lit a] [cv];
          mk_inst i2 ADD [Lit a; Lit b] [ev]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code ee Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (OK (jump_to cond_lbl
        (update_var ev (a+b) (update_var cv a ee))),G',tn')
Proof
  strip_tac >>
  qabbrev_tac `u = update_var ev (a+b) (update_var cv a ee)` >>
  `run_inst_seq code ee = OK u` by
    (simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          eval_operand_def, exec_pure2_def, Abbr `u`]) >>
  `run_inst_seq_mem_ok code ee` by
    (simp[run_inst_seq_mem_ok_def, mk_inst_def,
          below_frontier_no_ranges, inst_dload_in_section_other,
          step_inst_base_opcode_eqs, eval_operand_def, exec_pure2_def]) >>
  qexistsl_tac [`Gf`,`tf`] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
     (OK (u with vs_inst_idx := 2),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 2,Gf,tf) []
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,get_instruction_def,allocas_from_def] >>
     qexists_tac `i3` >> simp[]) >>
  drule_all gas_origin_ptr_path_trans >>
  simp[jump_to_def,Abbr `u`]
QED

Theorem for_range_checked_entry_path_full:
  code = [mk_inst i ASSIGN [op1] [cv];
          mk_inst (i+1) SUB [op2;op1] [rv];
          mk_inst (i+2) cmp [op1;op2] [g1];
          mk_inst (i+3) ISZERO [Var g1] [z1];
          mk_inst (i+4) ASSERT [Var z1] [];
          mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (i+6) ISZERO [Var g2] [z2];
          mk_inst (i+7) ASSERT [Var z2] [];
          mk_inst (i+8) ADD [op1;Var rv] [ev]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  MEM cmp [SGT;GT] /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad1) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
  s5 = update_var g2 (bool_to_word bad2) s4 /\
  s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
  s7 = update_var ev (a+(b-a)) s6 /\ ~bad1 /\ ~bad2 /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code ee Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (OK (jump_to cond_lbl s7),G',tn')
Proof
  strip_tac >>
  `run_inst_seq code ee = OK s7` by
    (qspecl_then [`ee`,`<|bb_label := lbl; bb_instructions := code|>`]
       mp_tac for_checked_entry_finite >>
     pure_rewrite_tac [basic_block_accessors,basic_block_accfupds,combinTheory.K_THM] >>
     disch_then (drule_all o cj 3) >> simp[]) >>
  `run_inst_seq_mem_ok code ee` by
    (irule run_inst_seq_mem_ok_every >>
     Cases_on `cmp = SGT` >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  qexistsl_tac [`Gf`,`tf`] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
     (OK (s7 with vs_inst_idx := 9),Gf,tf)` by
    (Cases_on `cmp = SGT` >> gvs[] >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s7 with vs_inst_idx := 9,Gf,tf) []
     (OK (jump_to cond_lbl (s7 with vs_inst_idx := 9)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[update_var_def,get_instruction_def,allocas_from_def] >>
     conj_tac >- (qexists_tac `i+9` >> simp[]) >>
     gvs[allocas_from_def]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def]
QED

(* The two rejected checks share one selected successful prefix. *)
Theorem for_range_checked_reject_path_full:
  code = [mk_inst i ASSIGN [op1] [cv];
          mk_inst (i+1) SUB [op2;op1] [rv];
          mk_inst (i+2) cmp [op1;op2] [g1];
          mk_inst (i+3) ISZERO [Var g1] [z1];
          mk_inst (i+4) ASSERT [Var z1] [];
          mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (i+6) ISZERO [Var g2] [z2];
          mk_inst (i+7) ASSERT [Var z2] [];
          mk_inst (i+8) ADD [op1;Var rv] [ev]] /\
  bb.bb_instructions = code ++ tail /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  MEM cmp [SGT;GT] /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad1) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
  s5 = update_var g2 (bool_to_word bad2) s4 /\
  s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
  s7 = update_var ev (a+(b-a)) s6 /\ (bad1 \/ bad2) /\
  k = (if bad1 then 4 else 7) /\ u = (if bad1 then s4 else s6) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  op_taint tf (Var (if bad1 then z1 else z2)) = {} /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn (TAKE k code) ee Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (Abort Revert_abort (revert_state (set_returndata []
         (u with vs_inst_idx := k))),G',tn')
Proof
  strip_tac >>
  `run_inst_seq (TAKE k code) ee = OK u` by
    (qspecl_then [`ee`,`<|bb_label := lbl; bb_instructions := code|>`]
       mp_tac for_checked_entry_finite >>
     pure_rewrite_tac [basic_block_accessors,basic_block_accfupds,combinTheory.K_THM] >>
     disch_then (drule_all_then strip_assume_tac) >>
     Cases_on `bad1` >> gvs[]) >>
  `run_inst_seq_mem_ok (TAKE k code) ee` by
    (irule run_inst_seq_mem_ok_every >>
     Cases_on `bad1` >> Cases_on `cmp = SGT` >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  qexistsl_tac [`Gf`,`tf`] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
     (OK (u with vs_inst_idx := k),Gf,tf)` by
    (Cases_on `bad1` >> Cases_on `cmp = SGT` >> gvs[] >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := k,Gf,tf) []
     (Abort Revert_abort (revert_state (set_returndata []
        (u with vs_inst_idx := k))),Gf,tf)` by
    (irule exit_inst_origin_ptr >>
     conj_tac >- simp[exit_result_def] >>
     conj_tac >- (Cases_on `bad1` >> gvs[update_var_def]) >>
     qexistsl_tac [`bb`,`mk_inst (i+k) ASSERT
       [Var (if bad1 then z1 else z2)] []`] >>
     Cases_on `bad1` >>
     gvs[get_instruction_def,update_var_def,mk_inst_def,
         step_inst_non_invoke,step_inst_base_opcode_eqs,
         eval_operand_def,lookup_var_def,exit_result_def,
         gas_events_step_def,gas_count_step_def,
         mem_safe_step_non_invoke,below_frontier_no_ranges,
         inst_dload_in_section_other,finite_mapTheory.FLOOKUP_UPDATE] >>
     irule (SRULE [mk_inst_def] assert_ptr_inst_ok) >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[]
QED

Theorem for_range_incr_path_full:
  code = [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
          mk_inst i2 ASSIGN [Var nv] [cv]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
  lookup_var cv dd = SOME c /\
  ~ctx_has_dalloca ctx /\ allocas_from lo dd /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code dd Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
      (OK (jump_to cond_lbl
        (update_var cv (c+1w) (update_var nv (c+1w) dd))),G',tn')
Proof
  strip_tac >>
  qabbrev_tac `u = update_var cv (c+1w) (update_var nv (c+1w) dd)` >>
  `run_inst_seq code dd = OK u` by
    (simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          eval_operand_def, exec_pure2_def,lookup_var_def,update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE,Abbr `u`]) >>
  `run_inst_seq_mem_ok code dd` by
    (irule run_inst_seq_mem_ok_every >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  qexistsl_tac [`Gf`,`tf`] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
     (OK (u with vs_inst_idx := 2),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 2,Gf,tf) []
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,get_instruction_def,allocas_from_def] >>
     qexists_tac `i3` >> simp[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`]
QED

Theorem for_range_cond_path_full:
  code = [mk_inst j1 EQ [Var cv; Var ev] [dv]] /\
  bb = <|bb_label := lbl; bb_instructions := code ++
       [mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
  ~ctx_has_dalloca ctx /\ allocas_from lo cc /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code cc Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (cc,G,tn) []
      (OK (jump_to (if a=b then exit_lbl else body_lbl)
        (update_var dv (bool_to_word (a=b)) cc)),G',tn')
Proof
  strip_tac >>
  qabbrev_tac `u = update_var dv (bool_to_word (a=b)) cc` >>
  `run_inst_seq code cc = OK u` by
    (simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
          eval_operand_def,exec_pure2_def,Abbr `u`]) >>
  `run_inst_seq_mem_ok code cc` by
    (irule run_inst_seq_mem_ok_every >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  `op_taint tf (Var dv) = {}` by
    (qpat_x_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
       (qspec_then `ARB` mp_tac) >>
     simp[inst_seq_ptr_def,step_inst_base_opcode_eqs,mk_inst_def,
          eval_operand_def,exec_pure2_def] >> strip_tac >>
     gvs[step_taint_def,op_taint_def,set_var_taint_def,
         out_taint_def,mk_inst_def,eval_operand_def,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  qexistsl_tac [`Gf`,`tf`] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (cc,G,tn) []
     (OK (u with vs_inst_idx := 1),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 1,Gf,tf) []
     (OK (jump_to (if bool_to_word (a=b) <> 0w then exit_lbl else body_lbl)
          (u with vs_inst_idx := 1)),Gf,tf)` by
    (irule jnz_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,eval_operand_def,
          lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE,allocas_from_def] >>
     qexistsl_tac [`Var dv`,`j2`] >>
     gvs[get_instruction_def,update_var_def,eval_operand_def,
         lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`,bool_to_word_def]
QED

Theorem for_range_scalar_cond_path_full:
  let i = mk_inst j1 EQ [Var cv; Var ev] [dv];
      u = update_var dv (bool_to_word (a=b)) cc;
      Gf = step_prov PG G i u;
      tf = step_taint i cc u tn
  in
  bb = <|bb_label := lbl; bb_instructions :=
       [i; mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
  FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo cc ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (cc,G,tn) []
    (OK (jump_to (if a=b then exit_lbl else body_lbl) u),Gf,tf)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> gen_tac >>
  qabbrev_tac `i = mk_inst j1 EQ [Var cv; Var ev] [dv]` >>
  qabbrev_tac `u = update_var dv (bool_to_word (a=b)) cc` >>
  qabbrev_tac `Gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i cc u tn` >>
  `step_inst_base i cc = OK u` by
    simp[Abbr `i`,Abbr `u`,step_inst_base_opcode_eqs,mk_inst_def,
         exec_pure2_def,eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i cc` by
    (simp[Abbr `i`,ptr_inst_ok_def,access_ok_def,taint_ok_def,
          mk_inst_def,source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def,step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
          eval_operand_def,update_var_def,allocas_from_def,op_prov_def] >>
     gvs[allocas_from_def,finite_mapTheory.FLOOKUP_DEF,Abbr `u`,
         update_var_def] >> metis_tac[]) >>
  `inst_seq_ptr D lo ctx func PG G tn [i] cc Gf tf` by
    simp[inst_seq_ptr_def,Abbr `Gf`,Abbr `tf`] >>
  `run_inst_seq [i] cc = OK u` by simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok [i] cc` by
    (irule run_inst_seq_mem_ok_every >>
     simp[Abbr `i`,mk_inst_def,below_frontier_no_ranges,
          inst_dload_in_section_other]) >>
  `op_taint tf (Var dv) = {}` by
    simp[Abbr `tf`,Abbr `i`,step_taint_def,op_taint_def,
         set_var_taint_def,out_taint_def,mk_inst_def,eval_operand_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (cc,G,tn) []
     (OK (u with vs_inst_idx := 1),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 1,Gf,tf) []
     (OK (jump_to (if bool_to_word (a=b) <> 0w then exit_lbl else body_lbl)
          (u with vs_inst_idx := 1)),Gf,tf)` by
    (irule jnz_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,eval_operand_def,
          lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE,allocas_from_def] >>
     qexistsl_tac [`Var dv`,`j2`] >>
     gvs[Abbr `i`,get_instruction_def,update_var_def,eval_operand_def,
         lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`,bool_to_word_def]
QED

(* The compiler's range-variable write, with one fixed memory/ghost endpoint. *)
Theorem for_range_store_path_full:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid MSTORE [Var dst; Var cv] []) /\
  ~s.vs_halted /\ lookup_var dst s = SOME addr /\
  lookup_var cv s = SOME value /\ alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (w2n addr,sz) /\ 32 <= sz /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (mstore (w2n addr) value s with vs_inst_idx := SUC s.vs_inst_idx),G',tn')
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst iid MSTORE [Var dst; Var cv] []` >>
  qabbrev_tac `u = mstore (w2n addr) value s` >>
  qexistsl_tac [`step_prov PG G i u`,`step_taint i s u tn`] >> gen_tac >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`,Abbr `u`] >> irule step_MSTORE >>
     simp[eval_operand_def]) >>
  `inst_mem_below_frontier i s` by
    (simp[Abbr `i`] >> irule for_range_allocated_store_below >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`aid`,`w2n addr`,`sz`] >> simp[eval_operand_def,w2n_lt]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` by
    (simp[Abbr `i`,mk_inst_def] >>
     irule (SRULE [mk_inst_def,is_terminator_def]
       (Q.INST [`i` |-> `mk_inst iid MSTORE [Var dst; Var cv] []`]
          straight_line_origin_ptr_edge)) >>
     simp[GSYM mk_inst_def,inst_dload_in_section_def] >> metis_tac[]) >>
  `~u.vs_halted` by simp[Abbr `u`,mstore_def] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem for_range_literal_entry_path_full_valid:
  code = [mk_inst i1 ASSIGN [Lit a] [cv];
          mk_inst i2 ADD [Lit a; Lit b] [ev]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn code ee Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (OK (jump_to cond_lbl
        (update_var ev (a+b) (update_var cv a ee))),Gf,tf)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  qabbrev_tac `u = update_var ev (a+b) (update_var cv a ee)` >>
  `run_inst_seq code ee = OK u` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,Abbr `u`] >>
  `run_inst_seq_mem_ok code ee` by
    simp[run_inst_seq_mem_ok_def,mk_inst_def,
         below_frontier_no_ranges,inst_dload_in_section_other,
         step_inst_base_opcode_eqs,eval_operand_def,exec_pure2_def] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
     (OK (u with vs_inst_idx := 2),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 2,Gf,tf) []
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,get_instruction_def,allocas_from_def] >>
     qexists_tac `i3` >> simp[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`]
QED


Theorem for_range_cond_path_full_valid:
  code = [mk_inst j1 EQ [Var cv; Var ev] [dv]] /\
  bb = <|bb_label := lbl; bb_instructions := code ++
       [mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
  ~ctx_has_dalloca ctx /\ allocas_from lo cc /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn code cc Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (cc,G,tn) []
      (OK (jump_to (if a=b then exit_lbl else body_lbl)
        (update_var dv (bool_to_word (a=b)) cc)),Gf,tf)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  qabbrev_tac `u = update_var dv (bool_to_word (a=b)) cc` >>
  `run_inst_seq code cc = OK u` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,Abbr `u`] >>
  `run_inst_seq_mem_ok code cc` by
    (irule run_inst_seq_mem_ok_every >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  `op_taint tf (Var dv) = {}` by
    (qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >>
     simp[NoAsms,inst_seq_ptr_def] >>
     gvs[inst_seq_ptr_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,step_taint_def,op_taint_def,
         set_var_taint_def,out_taint_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (cc,G,tn) []
     (OK (u with vs_inst_idx := 1),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 1,Gf,tf) []
     (OK (jump_to (if bool_to_word (a=b) <> 0w then exit_lbl else body_lbl)
          (u with vs_inst_idx := 1)),Gf,tf)` by
    (irule jnz_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,eval_operand_def,
          lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE,allocas_from_def] >>
     qexistsl_tac [`Var dv`,`j2`] >>
     gvs[get_instruction_def,update_var_def,eval_operand_def,
         lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  drule_all gas_origin_ptr_path_trans >>
  simp[jump_to_def,Abbr `u`,bool_to_word_def]
QED

Theorem for_range_checked_entry_path_full_valid:
  code = [mk_inst i ASSIGN [op1] [cv];
          mk_inst (i+1) SUB [op2;op1] [rv];
          mk_inst (i+2) cmp [op1;op2] [g1];
          mk_inst (i+3) ISZERO [Var g1] [z1];
          mk_inst (i+4) ASSERT [Var z1] [];
          mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (i+6) ISZERO [Var g2] [z2];
          mk_inst (i+7) ASSERT [Var z2] [];
          mk_inst (i+8) ADD [op1;Var rv] [ev]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  MEM cmp [SGT;GT] /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad1) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
  s5 = update_var g2 (bool_to_word bad2) s4 /\
  s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
  s7 = update_var ev (a+(b-a)) s6 /\ ~bad1 /\ ~bad2 /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn code ee Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (OK (jump_to cond_lbl s7),Gf,tf)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `run_inst_seq code ee = OK s7` by
    (qspecl_then [`ee`,`<|bb_label := lbl; bb_instructions := code|>`]
       mp_tac for_checked_entry_finite >>
     pure_rewrite_tac [basic_block_accessors,basic_block_accfupds,combinTheory.K_THM] >>
     disch_then (drule_all o cj 3) >> simp[]) >>
  `run_inst_seq_mem_ok code ee` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `cmp = SGT` >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
     (OK (s7 with vs_inst_idx := 9),Gf,tf)` by
    (Cases_on `cmp = SGT` >> gvs[] >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s7 with vs_inst_idx := 9,Gf,tf) []
     (OK (jump_to cond_lbl (s7 with vs_inst_idx := 9)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[update_var_def,get_instruction_def,allocas_from_def] >>
     conj_tac >- (qexists_tac `i+9` >> simp[]) >> gvs[allocas_from_def]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def]
QED

Theorem for_range_checked_reject_path_full_valid:
  code = [mk_inst i ASSIGN [op1] [cv];
          mk_inst (i+1) SUB [op2;op1] [rv];
          mk_inst (i+2) cmp [op1;op2] [g1];
          mk_inst (i+3) ISZERO [Var g1] [z1];
          mk_inst (i+4) ASSERT [Var z1] [];
          mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (i+6) ISZERO [Var g2] [z2];
          mk_inst (i+7) ASSERT [Var z2] [];
          mk_inst (i+8) ADD [op1;Var rv] [ev]] /\
  bb.bb_instructions = code ++ tail /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  MEM cmp [SGT;GT] /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad1) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
  s5 = update_var g2 (bool_to_word bad2) s4 /\
  s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
  s7 = update_var ev (a+(b-a)) s6 /\ (bad1 \/ bad2) /\
  k = (if bad1 then 4 else 7) /\ u = (if bad1 then s4 else s6) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  op_taint tf (Var (if bad1 then z1 else z2)) = {} /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn (TAKE k code) ee Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (Abort Revert_abort (revert_state (set_returndata []
         (u with vs_inst_idx := k))),Gf,tf)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `run_inst_seq (TAKE k code) ee = OK u` by
    (qspecl_then [`ee`,`<|bb_label := lbl; bb_instructions := code|>`]
       mp_tac for_checked_entry_finite >>
     pure_rewrite_tac [basic_block_accessors,basic_block_accfupds,combinTheory.K_THM] >>
     disch_then (drule_all_then strip_assume_tac) >>
     Cases_on `bad1` >> gvs[]) >>
  `run_inst_seq_mem_ok (TAKE k code) ee` by
    (irule run_inst_seq_mem_ok_every >>
     Cases_on `bad1` >> Cases_on `cmp = SGT` >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
     (OK (u with vs_inst_idx := k),Gf,tf)` by
    (Cases_on `bad1` >> Cases_on `cmp = SGT` >> gvs[] >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := k,Gf,tf) []
     (Abort Revert_abort (revert_state (set_returndata []
        (u with vs_inst_idx := k))),Gf,tf)` by
    (irule exit_inst_origin_ptr >>
     conj_tac >- simp[exit_result_def] >>
     conj_tac >- (Cases_on `bad1` >> gvs[update_var_def]) >>
     qexistsl_tac [`bb`,`mk_inst (i+k) ASSERT
       [Var (if bad1 then z1 else z2)] []`] >>
     Cases_on `bad1` >>
     gvs[get_instruction_def,update_var_def,mk_inst_def,
         step_inst_non_invoke,step_inst_base_opcode_eqs,
         eval_operand_def,lookup_var_def,exit_result_def,
         gas_events_step_def,gas_count_step_def,
         mem_safe_step_non_invoke,below_frontier_no_ranges,
         inst_dload_in_section_other,finite_mapTheory.FLOOKUP_UPDATE] >>
     irule (SRULE [mk_inst_def] assert_ptr_inst_ok) >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[]
QED

Theorem for_range_checked_reject_path_from_code:
  !code j op1 cv op2 rv cmp g1 z1 g2 z2 bound ev.
  code = [mk_inst (j+2) ASSIGN [op1] [cv];
          mk_inst (j+3) SUB [op2;op1] [rv];
          mk_inst (j+4) cmp [op1;op2] [g1];
          mk_inst (j+5) ISZERO [Var g1] [z1];
          mk_inst (j+6) ASSERT [Var z1] [];
          mk_inst (j+7) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (j+8) ISZERO [Var g2] [z2];
          mk_inst (j+9) ASSERT [Var z2] [];
          mk_inst (j+10) ADD [op1;Var rv] [ev]] ==>
  !DF lo explicit ctx func PG ee G tn Gf tf bb tail lbl a b bad1 bad2
   s1 s2 s3 s4 s5 s6 s7 k u cx st0 es.
  bb.bb_instructions = code ++ tail /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  MEM cmp [SGT;GT] /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad1) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
  s5 = update_var g2 (bool_to_word bad2) s4 /\
  s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
  s7 = update_var ev (a+(b-a)) s6 /\ (bad1 \/ bad2) /\
  k = (if bad1 then 4 else 7) /\ u = (if bad1 then s4 else s6) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  op_taint tf (Var (if bad1 then z1 else z2)) = {} /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn (TAKE k code) ee Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (Abort Revert_abort (revert_state (set_returndata []
         (u with vs_inst_idx := k))),Gf,tf)
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `i = j+2` >>
  `code = [mk_inst i ASSIGN [op1] [cv];
          mk_inst (i+1) SUB [op2;op1] [rv];
          mk_inst (i+2) cmp [op1;op2] [g1];
          mk_inst (i+3) ISZERO [Var g1] [z1];
          mk_inst (i+4) ASSERT [Var z1] [];
          mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (i+6) ISZERO [Var g2] [z2];
          mk_inst (i+7) ASSERT [Var z2] [];
          mk_inst (i+8) ADD [op1;Var rv] [ev]]` by
    simp[Abbr `i`,arithmeticTheory.ADD_ASSOC] >>
  gen_tac >> disch_tac >>
  drule_at (Pat `code = _`) for_range_checked_reject_path_full_valid >>
  disch_then irule >> gvs[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cx`,`es`,`st0`] >> simp[]
QED

Theorem for_range_checked_entry_path_from_code:
  !code j op1 cv op2 rv cmp g1 z1 g2 z2 bound ev.
  code = [mk_inst (j+2) ASSIGN [op1] [cv];
          mk_inst (j+3) SUB [op2;op1] [rv];
          mk_inst (j+4) cmp [op1;op2] [g1];
          mk_inst (j+5) ISZERO [Var g1] [z1];
          mk_inst (j+6) ASSERT [Var z1] [];
          mk_inst (j+7) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (j+8) ISZERO [Var g2] [z2];
          mk_inst (j+9) ASSERT [Var z2] [];
          mk_inst (j+10) ADD [op1;Var rv] [ev]] ==>
  !DF lo explicit ctx func PG ee G tn Gf tf bb lbl cond_lbl a b bad1 bad2
   s1 s2 s3 s4 s5 s6 s7 cx st0 es.
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst (j+11) JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  MEM cmp [SGT;GT] /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad1) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
  s5 = update_var g2 (bool_to_word bad2) s4 /\
  s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
  s7 = update_var ev (a+(b-a)) s6 /\ ~bad1 /\ ~bad2 /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn code ee Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (ee,G,tn) []
      (OK (jump_to cond_lbl s7),Gf,tf)
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `i = j+2` >>
  `code = [mk_inst i ASSIGN [op1] [cv];
          mk_inst (i+1) SUB [op2;op1] [rv];
          mk_inst (i+2) cmp [op1;op2] [g1];
          mk_inst (i+3) ISZERO [Var g1] [z1];
          mk_inst (i+4) ASSERT [Var z1] [];
          mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
          mk_inst (i+6) ISZERO [Var g2] [z2];
          mk_inst (i+7) ASSERT [Var z2] [];
          mk_inst (i+8) ADD [op1;Var rv] [ev]]` by
    simp[Abbr `i`,arithmeticTheory.ADD_ASSOC] >>
  gen_tac >> disch_tac >>
  drule_at (Pat `code = _`) for_range_checked_entry_path_full_valid >>
  disch_then irule >> gvs[Abbr `i`,arithmeticTheory.ADD_ASSOC] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cx`,`es`,`st0`] >> simp[]
QED

Theorem for_range_literal_scalar_entry_full:
  let i = mk_inst i1 ASSIGN [Lit a] [cv];
      j = mk_inst i2 ADD [Lit a; Lit b] [ev];
      s1 = update_var cv a ee;
      s2 = update_var ev (a+b) s1;
      G1 = step_prov PG G i s1;
      t1 = step_taint i ee s1 tn;
      G2 = step_prov PG G1 j s2;
      t2 = step_taint j s1 s2 t1
  in
  bb = <|bb_label := lbl; bb_instructions :=
       [i;j;mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\ cv <> ev ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (ee,G,tn) []
       (OK (jump_to cond_lbl s2),G2,t2)) /\
  lookup_var cv (jump_to cond_lbl s2) = SOME a /\
  lookup_var ev (jump_to cond_lbl s2) = SOME (a+b) /\
  FLOOKUP G2 cv = NONE /\ FLOOKUP G2 ev = NONE /\
  op_taint t2 (Var cv) = {} /\ op_taint t2 (Var ev) = {} /\
  t2.t_mem = tn.t_mem /\ t2.t_stor = tn.t_stor /\
  t2.t_trans = tn.t_trans /\ t2.t_imm = tn.t_imm /\
  (!v. v <> cv /\ v <> ev ==>
       lookup_var v (jump_to cond_lbl s2) = lookup_var v ee /\
       FLOOKUP G2 v = FLOOKUP G v /\
       op_taint t2 (Var v) = op_taint tn (Var v))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `i = mk_inst i1 ASSIGN [Lit a] [cv]` >>
  qabbrev_tac `j = mk_inst i2 ADD [Lit a;Lit b] [ev]` >>
  qabbrev_tac `s1 = update_var cv a ee` >>
  qabbrev_tac `s2 = update_var ev (a+b) s1` >>
  `!s u tn. step_taint i s (update_var cv a s) tn =
       tn with t_var := tn.t_var |+ (cv,{})` by
    (rpt gen_tac >> simp[Abbr `i`,Abbr `j`] >> irule for_checked_scalar_step_taint >>
     simp[op_taint_def,new_site_bytes_def,update_var_def,finite_mapTheory.FLOOKUP_DEF] >> SET_TAC[]) >>
  `!tn. step_taint j s1 s2 tn = tn with t_var := tn.t_var |+ (ev,{})` by
    (gen_tac >> simp[Abbr `i`,Abbr `j`] >> irule for_checked_scalar_step_taint >>
     conj_tac >- (rpt strip_tac >> gvs[op_taint_def]) >>
     simp[Abbr `s2`,new_site_bytes_def,update_var_def,finite_mapTheory.FLOOKUP_DEF] >> SET_TAC[]) >>
  `!G u. step_prov PG G i u = DRESTRICT G (COMPL {cv})` by
    (rpt gen_tac >> simp[Abbr `i`,Abbr `j`] >> irule for_checked_scalar_step_prov >>
     simp[] >> rpt strip_tac >> gvs[op_prov_def]) >>
  `!G u. step_prov PG G j u = DRESTRICT G (COMPL {ev})` by
    (rpt gen_tac >> simp[Abbr `i`,Abbr `j`] >> irule for_checked_scalar_step_prov >>
     simp[] >> rpt strip_tac >> gvs[op_prov_def]) >>
  reverse conj_tac
  >- simp[Abbr `s2`,Abbr `s1`,jump_to_def,update_var_def,lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FLOOKUP_DRESTRICT,
          op_taint_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i;j] ee
       (step_prov PG (step_prov PG G i s1) j s2)
       (step_taint j s1 s2 (step_taint i ee s1 tn))` by
    (gen_tac >>
     simp[inst_seq_ptr_def,Abbr `i`,Abbr `j`,Abbr `s1`,Abbr `s2`,
          step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def,exec_pure2_def] >>
     simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,
          source_memory_write_ranges_def,source_memory_read_ranges_def,
          GSYM mk_inst_def,step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def,
          exec_pure2_def,update_var_def,allocas_from_def] >>
     gen_tac >> Cases_on `op` >> simp[op_taint_def]) >>
  gen_tac >>
  `run_inst_seq [i;j] ee = OK s2` by
    simp[run_inst_seq_def,Abbr `i`,Abbr `j`,Abbr `s1`,Abbr `s2`,
         step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def,exec_pure2_def] >>
  `run_inst_seq_mem_ok [i;j] ee` by
    simp[run_inst_seq_mem_ok_def,Abbr `i`,Abbr `j`,mk_inst_def,
         below_frontier_no_ranges,inst_dload_in_section_other,
         step_inst_base_opcode_eqs,eval_operand_def,exec_pure2_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (ee,G,tn) []
    (OK (s2 with vs_inst_idx := 2),step_prov PG (step_prov PG G i s1) j s2,
       step_taint j s1 s2 (step_taint i ee s1 tn))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[Abbr `i`,Abbr `j`,mk_inst_def,is_terminator_def] >>
     disch_then irule >>
     conj_tac >- (qexists_tac `bb` >> gvs[mk_inst_def]) >>
     gvs[GSYM mk_inst_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s2 with vs_inst_idx := 2,step_prov PG (step_prov PG G i s1) j s2,
       step_taint j s1 s2 (step_taint i ee s1 tn)) []
    (OK (jump_to cond_lbl (s2 with vs_inst_idx := 2)),
       step_prov PG (step_prov PG G i s1) j s2,
       step_taint j s1 s2 (step_taint i ee s1 tn))` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `s2`,Abbr `s1`,update_var_def,get_instruction_def,allocas_from_def] >>
     qexists_tac `i3` >> simp[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def]
QED

Theorem for_range_literal_scalar_entry_endpoint_full:
  let i = mk_inst i1 ASSIGN [Lit a] [cv];
      j = mk_inst i2 ADD [Lit a; Lit (z-a)] [ev];
      s1 = update_var cv a ee;
      s2 = update_var ev z s1;
      G1 = step_prov PG G i s1;
      t1 = step_taint i ee s1 tn;
      G2 = step_prov PG G1 j s2;
      t2 = step_taint j s1 s2 t1
  in
  lookup_block lbl func.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions := [i;j;mk_inst i3 JMP [Label cond_lbl] []]|> /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo ee /\ cv <> ev ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (ee,G,tn) []
       (OK (jump_to cond_lbl s2),G2,t2)) /\
  lookup_var cv (jump_to cond_lbl s2) = SOME a /\
  lookup_var ev (jump_to cond_lbl s2) = SOME z /\
  FLOOKUP G2 cv = NONE /\ FLOOKUP G2 ev = NONE /\
  op_taint t2 (Var cv) = {} /\ op_taint t2 (Var ev) = {} /\
  t2.t_mem = tn.t_mem /\ t2.t_stor = tn.t_stor /\
  t2.t_trans = tn.t_trans /\ t2.t_imm = tn.t_imm /\
  (!v. v <> cv /\ v <> ev ==>
       lookup_var v (jump_to cond_lbl s2) = lookup_var v ee /\
       FLOOKUP G2 v = FLOOKUP G v /\
       op_taint t2 (Var v) = op_taint tn (Var v))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `SOME bb` >>
  mp_tac (Q.INST [`b` |-> `z-a`] (SPEC_ALL for_range_literal_scalar_entry_full)) >>
  simp[LET_THM,Abbr `bb`,GSYM wordsTheory.WORD_ADD_SUB_ASSOC,
       wordsTheory.WORD_ADD_SUB2]
QED

Theorem for_range_body_slot_preserved:
  !sb0 q G tn s G1 tn1 t sz.
    not_fresh_at sb0 q /\ ptr_covers G tn q s sz /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at sb0 x ==>
      FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) ==>
    ptr_covers G1 tn1 q t sz
Proof
  rpt strip_tac >>
  irule bodyFullForRangeSlotTheory.for_range_body_slot_preserved >>
  metis_tac[]
QED

(* Exact ordinary input retained for the related interior shadow packet. *)
Theorem for_range_lit_parts_exact_full:
  !cenv lctx ty id fty a1 n1 a2 n2 bound stmts st st' func.
    compile_stmt cenv lctx ty
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) st = ((),st') /\
    cenv.ce_alloca_locals /\ fn_has_code st st' func /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
       cs_extends sa sb) ==>
    ?p cv ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl bc sb0 sb1 sj nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 2)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 3)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc,st with cs_next_var := st.cs_next_var + 1) /\
      sb0 = st with <|
        cs_next_var := st.cs_next_var + 4;
        cs_next_label := st.cs_next_label + 5;
        cs_next_id := st.cs_next_id + 8;
        cs_current_bb := body_lbl;
        cs_current_insts := [mk_inst (st.cs_next_id + 7) MSTORE [Var p;Var cv] []];
        cs_blocks :=
          <|bb_label := cond_lbl; bb_instructions :=
            [mk_inst (st.cs_next_id + 5) EQ [Var cv;Var ev] [dv];
             mk_inst (st.cs_next_id + 6) JNZ
               [Var dv;Label exit_lbl;Label body_lbl] []]|> ::
          <|bb_label := entry_lbl; bb_instructions :=
            [mk_inst (st.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
             mk_inst (st.cs_next_id + 3) ADD
               [Lit (i2w n1);Lit (i2w n2 - i2w n1)] [ev];
             mk_inst (st.cs_next_id + 4) JMP [Label cond_lbl] []]|> ::
          <|bb_label := st.cs_current_bb; bb_instructions :=
            st.cs_current_insts ++
            [mk_inst st.cs_next_id ALLOCA
               [Lit (n2w (type_memory_bytes cenv fty))] [p]] ++
            [mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> ::
          st.cs_blocks|> /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts = [mk_inst (st.cs_next_id + 7) MSTORE [Var p;Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 4 /\ cs_extends st sb0 /\
      st.cs_next_id <= sb0.cs_next_id /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks = SOME
        <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
          [mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv fty))] [p];
           mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
      lookup_block entry_lbl func.fn_blocks = SOME
        <|bb_label := entry_lbl; bb_instructions :=
          [mk_inst (st.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
           mk_inst (st.cs_next_id + 3) ADD [Lit (i2w n1);Lit (i2w n2 - i2w n1)] [ev];
           mk_inst (st.cs_next_id + 4) JMP [Label cond_lbl] []]|> /\
      lookup_block cond_lbl func.fn_blocks = SOME
        <|bb_label := cond_lbl; bb_instructions :=
          [mk_inst (st.cs_next_id + 5) EQ [Var cv;Var ev] [dv];
           mk_inst (st.cs_next_id + 6) JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
        get_instruction bbb 0 = SOME (mk_inst (st.cs_next_id + 7) MSTORE [Var p;Var cv] [])) /\
      (~block_is_terminated sb1 ==>
        sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
        sj.cs_current_insts = sb1.cs_current_insts ++
          [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks = SOME
        <|bb_label := incr_lbl; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv;Lit 1w] [nv];
           mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
           mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
      st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def,lower_value_int_lit,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM] >>
  Cases_on `declare_local cenv id fty st` >> rename1 `_ = (bc,st1)` >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >> gvs[] >>
  simp[emit_local_alloca_def,fresh_label_def,emit_inst_def,emit_op_def,
       emit_void_def,fresh_id_def,emit_def,new_block_def,fresh_var_def,
       emit_jmp_if_not_terminated_def,comp_get_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_stmts bc _ ty stmts _ = ((),sb1)` >>
  qpat_x_assum `(if block_is_terminated sb1 then _ else _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [comp_bind_def,comp_return_def,
      fresh_id_def,emit_def,LET_THM]) >>
  rename1 `_ = ((),sj)` >>
  qmatch_asmsub_abbrev_tac `compile_stmts bc _ ty stmts sb0 = _` >>
  strip_tac >> qexists_tac `sj` >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  `cs_extends st sb0` by
    (simp[cs_extends_def,Abbr `sb0`] >> qexists_tac `[_;_;_]` >> simp[]) >>
  `sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
   sj.cs_next_var = sb1.cs_next_var /\ cs_extends sb1 sj /\
   (~block_is_terminated sb1 ==> sj.cs_current_insts = sb1.cs_current_insts ++
     [mk_inst sb1.cs_next_id JMP
       [Label (fresh_label_output "for_incr" (st.cs_next_label + 3))] []])` by
    (Cases_on `block_is_terminated sb1` >>
     fs[comp_return_def,comp_bind_def,fresh_id_def,emit_def,LET_THM] >>
     gvs[cs_extends_refl] >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends sj st'` by
    (qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[cs_extends_def] >>
     qexists_tac `[_;<|bb_label := sj.cs_current_bb;
       bb_instructions := sj.cs_current_insts|>]` >> simp[]) >>
  `?nb. sb1.cs_blocks = nb ++ sb0.cs_blocks` by
    (qpat_x_assum `cs_extends sb0 sb1` mp_tac >> simp[cs_extends_def] >> metis_tac[]) >>
  `!l b. MEM b (emitted_blocks st st') /\ b.bb_label = l ==>
    lookup_block l func.fn_blocks = SOME b` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `emitted_blocks st st' =
    [HD st'.cs_blocks;HD (TL st'.cs_blocks)] ++ nb ++
    [HD sb0.cs_blocks;HD (TL sb0.cs_blocks);HD (TL (TL sb0.cs_blocks))]` by
    (irule emitted_blocks_append >>
     qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[Abbr `sb0`]) >>
  `cs_extends sb1 st' /\ cs_extends sb0 st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func` by
    metis_tac[fn_has_code_mid,cs_extends_trans] >>
  `?bbb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bbb /\
    isPREFIX sb0.cs_current_insts bbb.bb_instructions` by metis_tac[fn_has_code_start] >>
  qpat_x_assum `_ = st'` (assume_tac o SYM) >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND,MEM] >> disj2_tac >> disj2_tac >> disj2_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND,MEM] >> disj2_tac >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND,MEM] >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qexists_tac `bbb` >>
      qpat_x_assum `lookup_block sb0.cs_current_bb _ = _` mp_tac >>
      qpat_x_assum `isPREFIX sb0.cs_current_insts _` mp_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
      Cases_on `bbb.bb_instructions` >> fs[get_instruction_def])
  >- (strip_tac >> qpat_x_assum `~block_is_terminated sb1 ==> _` drule >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND,MEM] >> disj1_tac >> disj1_tac >> disj1_tac >>
      qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >> simp_tac (srw_ss()) [])
  >- (qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >> simp_tac (srw_ss()) []) >>
  qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >> simp_tac (srw_ss()) []
QED

Theorem body_for_range_lit_full:
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >> gvs[] >> rename1 `For id typ _ n stmts` >>
  `id NOTIN FDOM env.var_types /\ is_int_type typ /\
   well_typed_literal typ (IntL n1) /\ well_typed_literal typ (IntL n2) /\
   well_formed_type env.type_defs typ /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def,well_typed_iterator_def,well_typed_expr_def,
        expr_type_def,optionTheory.IS_SOME_EXISTS,AllCaseEqs()] >>
  `n1 <= n2 /\ n = Num (n2-n1) /\ supported_stmts tops bindings stmts` by
    gvs[supported_stmt_def,supported_iterator_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def,optionTheory.IS_SOME_EXISTS] >>
  `GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)) <> [] ==>
   body_stmts_full_ok cx stmts` by
    (strip_tac >>
     qpat_x_assum `!s'' tyv t s3 vs t' s4 t''. _`
       (qspecl_then [`es`,`tyv`,`es`,`es`,
         `GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))`,
         `es`,`es`,`es`] mp_tac) >>
     simp[lift_option_type_def,return_def,eval_iterator_range_lit,
          check_def,assert_def,compatible_bound_def,body_for_full_ok_def] >>
     disch_then irule >> qexistsl_tac [`es`,`IntV n1`,`es`] >>
     Cases_on `Num (n2-n1)` >> gvs[GENLIST_CONS,read_result_def,return_def]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `eval_stmt cx
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n stmts) =
   eval_for cx tyv id stmts
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))` by
    simp[FUN_EQ_THM,Once evaluate_def,eval_iterator_range_lit,
         bind_def,ignore_bind_def,lift_option_type_def,lift_option_def,
         return_def,check_def,assert_def,compatible_bound_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (For _ _ _ _ _) sa = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,pairTheory.pair_case_eq] >>
  strip_tac >>
  Cases_on `compile_stmt cenv lctx ret_ty
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
      (Num (n2-n1)) stmts) sa` >>
  Cases_on `q` >> gvs[] >>
  drule for_range_lit_parts_exact_full >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[compile_stmt_cs_mono,cs_mono_def])) >>
  strip_tac >>
  Cases_on `stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0` >>
  rename1 `stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 =
    (bc_out, sb_body)` >>
  `sb_body = sb1` by
    metis_tac[stmtSimPropsTheory.compile_stmts_env,pairTheory.SND] >>
  qpat_x_assum `sb_body = sb1` SUBST_ALL_TAC >>
  `!shadow_sb0. gas_shadow_state sb0 shadow_sb0 ==>
    FST (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty
      (MAP gas_shadow_stmt stmts) shadow_sb0) = bc_out /\
    gas_shadow_state sb1
      (SND (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty
        (MAP gas_shadow_stmt stmts) shadow_sb0))` by
    (gen_tac >> disch_tac >>
     mp_tac (Q.SPECL [`stmts`,`bc`,`InLoop exit_lbl incr_lbl`,`ret_ty`]
       gas_shadow_stmts_env) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sb0`,`shadow_sb0`] mp_tac) >>
     pure_asm_rewrite_tac [pairTheory.FST,pairTheory.SND] >> metis_tac[]) >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) shadow_sa = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,gas_shadow_stmt_def,
       gas_shadow_iterator_def,gas_shadow_expr_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `shadow_sa.cs_next_var = sa.cs_next_var` by
    (qpat_x_assum `gas_shadow_state sa shadow_sa` mp_tac >>
     simp[gasShadowStateTheory.gas_shadow_state_def]) >>
  `declare_local cenv id typ shadow_sa =
    (bc,shadow_sa with cs_next_var := shadow_sa.cs_next_var + 1)` by
    (qpat_x_assum `declare_local cenv id typ sa = _` mp_tac >>
     simp[declare_local_def,fresh_var_def,comp_bind_def,comp_return_def,
          LET_THM] >> strip_tac >>
     simp[]) >>
  `FLOOKUP bc.ce_vars id =
    SOME (PtrVar (Var (STRING #"%" (toString shadow_sa.cs_next_var)))
      (type_memory_bytes cenv typ))` by
    metis_tac[stmtSimPropsTheory.declare_local_ptr] >>
  qpat_x_assum `compile_stmt _ _ _ (For _ _ _ _ (MAP _ _)) shadow_sa = _`
    mp_tac >>
  simp[compile_stmt_def,lower_value_int_lit,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,LET_THM] >>
  simp[emit_local_alloca_def,fresh_label_def,emit_inst_def,emit_op_def,
       emit_void_def,fresh_id_def,emit_def,new_block_def,fresh_var_def,
       comp_get_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM] >>
  qmatch_goalsub_abbrev_tac `compile_stmts bc _ ret_ty
    (MAP gas_shadow_stmt stmts) shadow_body_in` >>
  pairarg_tac >> simp[] >>
  rename1 `compile_stmts bc _ ret_ty (MAP gas_shadow_stmt stmts)
    shadow_body_in = (shadow_unit,shadow_body_out)` >>
  pairarg_tac >> simp[] >> strip_tac >>
  `gas_shadow_state sb0 shadow_body_in` by
    (qpat_x_assum `sb0 = _` SUBST1_TAC >>
     qpat_x_assum `gas_shadow_state sa shadow_sa` mp_tac >>
     simp[gasShadowStateTheory.gas_shadow_state_def] >> strip_tac >>
     simp[Abbr `shadow_body_in`,gasShadowStateTheory.gas_shadow_state_def,
          gasShadowStateTheory.gas_shadow_block_def,
          gasShadowStateTheory.gas_shadow_inst_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     irule LIST_REL_APPEND_suff >>
     simp[gasShadowStateTheory.gas_shadow_inst_def]) >>
  `shadow_sa.cs_next_label = sa.cs_next_label` by
    metis_tac[gasShadowStateTheory.gas_shadow_state_def] >>
  `compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty
     (MAP gas_shadow_stmt stmts) shadow_body_in =
       (shadow_unit,shadow_body_out)` by
    (qpat_x_assum `compile_stmts _ _ _ (MAP _ _) _ = _` mp_tac >>
     simp[]) >>
  `stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty
     (MAP gas_shadow_stmt stmts) shadow_body_in = (bc_out,shadow_body_out)` by
    (qpat_x_assum `!shadow_sb0. _` (qspec_then `shadow_body_in` mp_tac) >>
     simp[] >> strip_tac >>
     metis_tac[stmtSimPropsTheory.compile_stmts_env,
       pairTheory.PAIR,pairTheory.FST,pairTheory.SND,pairTheory.PAIR_EQ]) >>
  `gas_shadow_state sb1 shadow_body_out` by metis_tac[pairTheory.SND] >>
  `cs_extends shadow_sa shadow_body_in` by
    (simp[cs_extends_def,Abbr `shadow_body_in`] >>
     qexists_tac `[_;_;_]` >> simp[]) >>
  `cs_extends shadow_body_in shadow_body_out` by
    metis_tac[compile_stmt_cs_mono,cs_mono_def] >>
  rename1 `emit_jmp_if_not_terminated _ shadow_body_out = (shadow_junit,shadow_j)` >>
  `cs_extends shadow_body_out shadow_j` by
    (qpat_x_assum `emit_jmp_if_not_terminated _ shadow_body_out = _` mp_tac >>
     simp[emit_jmp_if_not_terminated_def,comp_get_def,comp_bind_def] >>
     Cases_on `block_is_terminated shadow_body_out` >>
     simp[comp_return_def,cs_extends_refl] >>
     metis_tac[cs_extends_emit_inst]) >>
  `cs_extends shadow_j shadow_sb` by
    (qpat_x_assum `_ with <|cs_next_var := _; cs_next_id := _;
       cs_current_bb := _; cs_current_insts := []; cs_blocks := _|> = shadow_sb`
       (SUBST1_TAC o SYM) >>
     simp[cs_extends_def] >>
     qexists_tac `[_;<|bb_label := shadow_j.cs_current_bb;
       bb_instructions := shadow_j.cs_current_insts|>]` >> simp[]) >>
  `fn_has_code shadow_body_in shadow_body_out shadow_func` by
    metis_tac[fn_has_code_mid,cs_extends_trans] >>
  `type_memory_bytes cenv typ = 32` by
    (Cases_on `typ` >> gvs[] >> Cases_on `b` >> gvs[type_memory_bytes_def]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  qabbrev_tac `salloc = sa with <|
    cs_next_var := sa.cs_next_var + 1;
    cs_next_id := sa.cs_next_id + 1;
    cs_current_insts := sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]] |>` >>
  `compile_alloc_buffer 32 sa =
    (<|buf_operand := Var p; buf_size := 32|>,salloc)` by
    (simp[compile_alloc_buffer_def,emit_op_def,fresh_var_def,
          emit_inst_def,fresh_id_def,emit_def,comp_bind_def,
          comp_return_def,comp_ignore_bind_def,Abbr `salloc`] >> gvs[]) >>
  `fn_has_code sa salloc func` by
    (simp[fn_has_code_def,emitted_blocks_def,Abbr `salloc`] >>
     qexists_tac `<|bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts ++
         [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p];
          mk_inst (sa.cs_next_id + 1) JMP [Label entry_lbl] []]|>` >>
     simp[]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    fs[ghost_inv_at_def] >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
    strip_assume_tac) >>
  fs[buffer_accessors,operand_11] >>
  `~t.vs_halted` by
    (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|> = s0` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >>
     simp[]) >>
  `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G',tn') [] (OK (jump_to entry_lbl t),G',tn')` by
    (gen_tac >> irule jmp_origin_ptr_path >>
     fs[Abbr `salloc`] >> simp[get_instruction_def,EL_APPEND_EQN] >>
     qexists_tac `sa.cs_next_id + 1` >> simp[]) >>
  qabbrev_tac `e0 = jump_to entry_lbl t` >>
  qpat_assum `lookup_block entry_lbl _ = _`
    (mp_then Any (fn th => mp_tac (Q.INST
      [`ee` |-> `e0`, `G` |-> `G'`, `tn` |-> `tn'`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] (SPEC_ALL th)))
      (SRULE [LET_THM] for_range_literal_scalar_entry_endpoint_full)) >>
  (impl_tac >- (fs[Abbr `e0`,jump_to_def,allocas_from_def] >> metis_tac[])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_origin_ptr_path _ (e0,G',tn') [] (OK ec,Gentry,tnentry)` >>
  suspend "continuation"
QED

(* The entry prefixes are intentionally absent here.  The concrete slot,
   condition, body and backedge layout determine the common continuation. *)
Theorem for_range_continue_full:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (For id typ it n stmts) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (For id typ it n stmts) ==> occurs_abi_decode_target target tops) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ it n stmts) = SOME env' /\
  stmt_exprs_ok cenv (For id typ it n stmts) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ it n stmts)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)) <> [] ==>
    body_stmts_full_ok cx stmts) /\
  id NOTIN FDOM env.var_types /\ is_int_type typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  n1 <= n2 /\ Num (n2-n1) < dimword (:256) /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  type_memory_bytes cenv typ = 32 /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  q = STRING #"%" (toString sa.cs_next_var) /\
  not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
  (!x. not_fresh_at sa x ==> x <> cv /\ x <> dv) /\
  q <> cv /\ cv <> ev /\ q <> dv /\ cv <> dv /\ ev <> dv /\
  declare_local cenv id typ sa = (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) (fn_insts func) /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var cv; Var ev] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block body_lbl func.fn_blocks = SOME bbb /\
  get_instruction bbb 0 = SOME (mk_inst jstore MSTORE [Var q; Var cv] []) /\
  sb0.cs_current_bb = body_lbl /\
  sb0.cs_current_insts = [mk_inst jstore MSTORE [Var q; Var cv] []] /\
  sa.cs_next_var < sb0.cs_next_var /\ cs_extends sa sb0 /\
  compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = ((),sb1) /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb1) /\
  cs_extends sb0 sb1 /\ fn_has_code sb0 sb1 func /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts)
    shadow_body_in = (bc_out,shadow_body_out) /\
  gas_shadow_state sb0 shadow_body_in /\ gas_shadow_state sb1 shadow_body_out /\
  fn_has_code shadow_body_in shadow_body_out shadow_func /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func) /\
  sj.cs_next_var = sb1.cs_next_var /\ nv = STRING #"%" (toString sj.cs_next_var) /\
  lookup_block incr_lbl func.fn_blocks = SOME
    <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
  r.cs_current_bb = exit_lbl /\ r.cs_current_insts = [] /\
  sa.cs_next_var <= r.cs_next_var /\ ~block_is_terminated r /\
  storage_trace_domain cx st0 es.storage_trace /\
  gas_admissible (eval_for cx tyv id stmts
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))) (stmt_res_ok lctx) es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    expr_sim_inv cenv cx env es /\ stmt_state_rel H ctx func cenv cx es ec /\
    storage_well_formed_on cx es (FST H) /\
    return_buf_frame d cenv sa ec /\ alloca_history func ec /\
    s0.vs_alloca_next <= ec.vs_alloca_next /\ allocas_from lo ec /\
    ghost_inv_at (DF H) lo d cenv cx es Gentry tnentry ec /\
    ~ec.vs_halted /\ ec.vs_current_bb = cond_lbl /\ ec.vs_inst_idx = 0 /\
    lookup_var q ec = SOME w /\ ptr_covers Gentry tnentry q ec 32 /\
    FLOOKUP ec.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= ec.vs_alloca_next /\
    (!name b len. local_region cenv es.scopes ec name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP Gentry cv = NONE /\ FLOOKUP Gentry ev = NONE /\
    op_taint tnentry (Var cv) = {} /\ op_taint tnentry (Var ev) = {} /\
    lookup_var ev ec = SOME (i2w n2) /\ lookup_var cv ec = SOME (i2w n1) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x ec = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP ec.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gentry x = FLOOKUP G0 x /\
      op_taint tnentry (Var x) = op_taint tn0 (Var x))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))))
    (es,ec,Gentry,tnentry)
    (\H res ee G tn s. res = INL () /\
      stmt_lands lctx r (INL ()) s /\ ~s.vs_halted /\
      ~block_is_terminated r /\ cenv_top_ext cenv cenv ee.scopes /\
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv r s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
      (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP s.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt rr. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt rr)
Proof
  strip_tac >>
  qabbrev_tac `Inv = \H rs ee G tn s.
    expr_sim_inv cenv cx env ee /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    lookup_var q s = SOME w /\ ptr_covers G tn q s 32 /\
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    lookup_var ev s = SOME (i2w n2) /\
    (?k. k <= Num (n2-n1) /\
      rs = DROP k (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
      lookup_var cv s = SOME (i2w (n1 + &k)) /\
      n1 + &k <= n2 /\ Num (n2-n1) < dimword (:256)) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))` >>
  qabbrev_tac `Done = \H ee G tn s.
    stmt_lands lctx r (INL ()) s /\ ~s.vs_halted /\
    ~block_is_terminated r /\ cenv_top_ext cenv cenv ee.scopes /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv r s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))` >>
  (* Interface probe only: these are propositions, NOT assumptions.
     Concrete layout resources are the compile_for_range_lit_parts packet
     above: ALLOCA/JMP at sa, entry at entry_lbl, EQ/JNZ at cond_lbl,
     MSTORE at body_lbl, compile_stmts bc (InLoop exit_lbl incr_lbl)
     ret_ty stmts sb0 = ((),sb1), optional sb1->sj JMP, increment at
     incr_lbl, and r's empty exit block. No callback is a public premise.

     Init is used after composing the three already selected [] prefixes.
     Round is exactly eval_for_rounds_full's cons premise. Empty is its
     nil premise. The handler adapter's Q is RoundPost rs below. Its B
     is the ENTIRE existential stmt_frag_full post at bc/sb0/sb1, not an
     exterior-cenv projection. The body starts after the MSTORE, with
     cursor LENGTH sb0.cs_current_insts and the pushed scope, and typing
     environment extend_local env id typ F. Its final cenv'' must remain
     existential even on Break/Continue; only normal forces cenv''=bc_out.
     Compose cenv_top_ext cenv bc with bc->cenv'', then scope-pop to
     exterior cenv. expr_sim_inv_for_pop is used only for normal/Continue;
     Break uses Done and does not require a next-body expr_sim_inv.
     ExitPost is the adapter's successful-package transport obligation:
     a *single* u/G2/tn2 is selected before H. Normal/Continue execute the
     optional JMP and increment; Break already lands at exit_lbl. The
     separate stmt_exit_ptr branch keeps gt and propagates Return/errors.
     Certificate lifts are still independent obligations of rounds, not
     discharged by these typed propositions. *)
  qabbrev_tac `RoundPost = \rs H (res : bool + exception) ee G tn s.
    ee.gas_obs = [] /\ ~s.vs_halted /\
    ?b. res = INL b /\ (b ==> Done H ee G tn s) /\
      (~b ==> Inv H rs ee G tn s)` >>
  qabbrev_tac `BodyPost = \sstart Gstart tnstart H res ee G tn s.
    ?cenv''. stmt_lands (InLoop exit_lbl incr_lbl) sb1 res s /\
      ~s.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
      cenv_top_ext bc cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee s /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb1 s /\ alloca_history func s /\
      sstart.vs_alloca_next <= s.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn s /\
      (!x v. not_fresh_at sb0 x /\ lookup_var x sstart = SOME v ==>
        lookup_var x s = SOME v) /\
      (!aid bl. FLOOKUP sstart.vs_allocas aid = SOME bl ==>
        FLOOKUP s.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sb0 x ==>
        FLOOKUP G x = FLOOKUP Gstart x /\
        op_taint tn (Var x) = op_taint tnstart (Var x))` >>
  qabbrev_tac `InitObligation =
    !H. valid_horizon cx st0 H es.storage_trace ==>
      Inv H (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))
        es Gentry tnentry ec` >>
  qabbrev_tac `RoundObligation =
    !a rs ee s G tn.
      ~s.vs_halted /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        Inv H (a::rs) ee G tn s) /\
      gas_admissible (eval_for cx tyv id stmts (a::rs)) (stmt_res_ok lctx) ee ==>
      gas_outcome_full
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (do v <- read_result cx a;
            push_scope_with_var id tyv v;
            finally (try (do eval_stmts cx stmts; return F od)
                         handle_loop_exception) pop_scope od)
        (ee,s,G,tn) (RoundPost rs)
        (\H res ee gt rr. ?ex. res = INR ex /\
          !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt rr)` >>
  qabbrev_tac `EmptyObligation =
    !ee s G tn.
      ~s.vs_halted /\ storage_trace_domain cx st0 ee.storage_trace /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        Inv H [] ee G tn s) /\
      gas_admissible (eval_for cx tyv id stmts []) (stmt_res_ok lctx) ee ==>
      ?u G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path
          (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK u,G1,tn1) /\
        Done H (ee with gas_obs := []) G1 tn1 u` >>
  (* The following packet is to be produced by the concrete condition and
     store prefix, not assumed by the exported family. *)
  qabbrev_tac `BodyStart = \ee v H sstart Gstart tnstart.
    let pushed = (ee with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: ee.scopes)
      with gas_obs := [] in
    expr_sim_inv bc cx (extend_local env id typ F) pushed /\
    stmt_state_rel H ctx func bc cx pushed sstart /\
    storage_well_formed_on cx pushed (FST H) /\
    return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
    ghost_inv_at (DF H) lo d bc cx pushed Gstart tnstart sstart /\
    ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
    sstart.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ret_pc_ok bc sb0 sstart /\ allocas_from lo sstart /\
    lookup_var q sstart = SOME w /\ ptr_covers Gstart tnstart q sstart 32 /\
    FLOOKUP sstart.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= sstart.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes sstart name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP Gstart cv = NONE /\ FLOOKUP Gstart ev = NONE /\
    op_taint tnstart (Var cv) = {} /\ op_taint tnstart (Var ev) = {} /\
    lookup_var ev sstart = SOME (i2w n2) /\
    s0.vs_alloca_next <= sstart.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sstart = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP sstart.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gstart x = FLOOKUP G0 x /\
      op_taint tnstart (Var x) = op_taint tn0 (Var x))` >>
  qabbrev_tac `ExitPostObligation =
    !a rs ee s G tn k v sstart Gstart tnstart.
      storage_trace_domain cx st0 ee.storage_trace /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        Inv H (a::rs) ee G tn s) /\
      k < Num (n2-n1) /\ a = Value (IntV (n1 + &k)) /\
      rs = DROP (SUC k)
        (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
      v = IntV (n1 + &k) /\ read_result cx a ee = (INL v,ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path
          (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK sstart,Gstart,tnstart) /\
        BodyStart ee v H sstart Gstart tnstart /\
        lookup_var cv sstart = SOME (i2w (n1 + &k))) ==>
    !res mid G1 tn1 t gs.
      mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        BodyPost sstart Gstart tnstart H res mid G1 tn1 t) /\
      eval_stmts cx stmts
        ((ee with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tyv;
                            value := v; popped := []|>)) :: ee.scopes)
          with gas_obs := gs) = (res,mid) ==>
      (res = INL () \/ res = INR BreakException \/ res = INR ContinueException) /\
      ?u G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path
          (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t,G1,tn1) [] (OK u,G2,tn2) /\
        RoundPost rs H (INL (res = INR BreakException))
          (mid with scopes := TL mid.scopes) G2 tn2 u` >>
  `not_fresh_at sb0 q` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >>
  `!ss Gs tns H res mid G1 tn1 u.
    ptr_covers Gs tns q ss 32 /\
    BodyPost ss Gs tns H res mid G1 tn1 u ==>
    ptr_covers G1 tn1 q u 32` by
    (rpt strip_tac >>
     qpat_x_assum `BodyPost _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `BodyPost`] >> strip_tac >>
     irule for_range_body_slot_preserved >>
     qexistsl_tac [`Gs`,`ss`,`sb0`,`tns`] >> asm_rewrite_tac [] >>
     conj_tac >- (qpat_x_assum `not_fresh_at sb0 q` mp_tac >> simp[]) >>
     qpat_x_assum `ptr_covers Gs tns q ss 32` mp_tac >> simp[]) >>
  `!ss Gs tns res mid G1 tn1 u.
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      BodyPost ss Gs tns H res mid G1 tn1 u) ==>
    (res = INL () \/ res = INR BreakException \/ res = INR ContinueException)` by
    (rpt strip_tac >>
     `?H. valid_horizon cx st0 H mid.storage_trace` by
       metis_tac[storage_trace_domain_def] >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> BodyPost _ _ _ _ _ _ _ _ _`
       drule >>
     simp[Abbr `BodyPost`] >>
     strip_tac >>
     qpat_x_assum `stmt_lands _ _ res _` mp_tac >>
     simp_tac std_ss [stmt_lands_def] >> metis_tac[]) >>
  `InitObligation` by
    (simp_tac bool_ss [Abbr `InitObligation`,Abbr `Inv`] >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
     asm_rewrite_tac [] >> qexists_tac `0` >> simp[]) >>
  `EmptyObligation` by
    (simp_tac bool_ss [Abbr `EmptyObligation`] >>
     rpt gen_tac >> strip_tac >>
     simp_tac bool_ss [Abbr `Done`] >>
     irule (GEN_ALL (CONV_RULE (REDEPTH_CONV BETA_CONV)
       (PURE_REWRITE_RULE [LET_THM] for_range_literal_empty_full))) >>
     simp[for_range_scalar_cond_path_full |> PURE_REWRITE_RULE [LET_THM]
       |> CONV_RULE (REDEPTH_CONV BETA_CONV)] >>
     conj_tac >- fs[ret_pc_ok_def] >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        irule (GEN_ALL (CONV_RULE (REDEPTH_CONV BETA_CONV)
          (PURE_REWRITE_RULE [LET_THM] for_range_scalar_cond_path_full))) >>
        asm_rewrite_tac [] >> metis_tac[]) >>
     qexistsl_tac [`body_lbl`,`cond_lbl`,`cv`,`dv`,`env`,`ev`,
       `j1`,`j2`,`n1`,`n2`,`q`,`w`] >>
     asm_rewrite_tac [] >>
     `~not_fresh_at sa dv` by metis_tac[] >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> Inv _ _ _ _ _ _` mp_tac >>
     simp[Abbr `Inv`,loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >>
     disch_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >> simp[] >>
     conj_tac >- asm_rewrite_tac [] >>
     qexists_tac `k` >> fs[]) >>
  `!a rs ee s G tn.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      Inv H (a::rs) ee G tn s) ==>
    ?k sstart Gstart tnstart.
      k < Num (n2-n1) /\ a = Value (IntV (n1 + &k)) /\
      rs = DROP (SUC k)
        (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
      read_result cx a ee = (INL (IntV (n1 + &k)),ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path
          (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK sstart,Gstart,tnstart) /\
        BodyStart ee (IntV (n1 + &k)) H sstart Gstart tnstart /\
        lookup_var cv sstart = SOME (i2w (n1 + &k)))` by
    (simp_tac bool_ss [Abbr `Inv`,Abbr `BodyStart`,LET_THM] >>
     match_mp_tac (GEN_ALL (CONV_RULE (REDEPTH_CONV BETA_CONV)
       (PURE_REWRITE_RULE [LET_THM] for_range_literal_body_start_full))) >>
     qexistsl_tac [`jstore`,`j2`,`j1`,`exit_lbl`,`dv`,`body_lbl`,`bbb`] >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        irule (GEN_ALL (CONV_RULE (REDEPTH_CONV BETA_CONV)
          (PURE_REWRITE_RULE [LET_THM] for_range_scalar_cond_path_full))) >>
        asm_rewrite_tac [] >> metis_tac[]) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        mp_tac (GEN_ALL (CONV_RULE (REDEPTH_CONV BETA_CONV)
          (PURE_REWRITE_RULE [LET_THM] for_range_store_path_canonical_full))) >>
        disch_then drule_all >>
        metis_tac[]) >>
     simp[] >>
     metis_tac[]) >>
  `ExitPostObligation` by
    (simp_tac bool_ss [Abbr `ExitPostObligation`] >>
     rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     `!b P D I. (P /\ (?z. (INL b : bool + exception) = INL z /\
       (z ==> D) /\ (~z ==> I))) = (P /\ (b ==> D) /\ (~b ==> I))` by
       (rpt gen_tac >> Cases_on `b` >> simp[]) >>
     simp_tac (srw_ss() ++ CONJ_ss)
       [Abbr `RoundPost`,Abbr `Done`,Abbr `Inv`,CONJ_ASSOC] >>
     mp_tac (CONV_RULE
       (RAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [CONJ_ASSOC]))
       (Q.INST [`rs` |-> `DROP (SUC k) (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))`]
         (SPEC_ALL for_range_exit_post_layout_full))) >>
     (impl_tac >-
       (conj_tac >- metis_tac[body_inv_def] >>
        conj_tac >- metis_tac[body_inv_def] >>
        conj_tac >- fs[supported_stmt_def] >>
        rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
        conj_tac >- (irule range_value_has_type >>
          asm_rewrite_tac [] >> qexists_tac `n2` >> simp[]) >>
        rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
        conj_tac >-
          (qpat_assum `call_evaluation_safe _ _` mp_tac >>
           simp_tac bool_ss [vyperTypeCallGraphTheory.int_calls_stmt_def] >>
           metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]) >>
        rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
        conj_tac >- metis_tac[] >>
        rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
        conj_tac >- REFL_TAC >>
        conj_tac >-
          (gen_tac >> strip_tac >>
           qpat_assum `!H. _ ==> (\H rs ee G tn s. _) _ _ _ _ _ _`
             (qspec_then `H` mp_tac) >>
           simp_tac bool_ss [] >> asm_rewrite_tac [] >> strip_tac >>
           rename1 `_::_ = DROP j _` >>
           `j = k` by
             (qpat_assum `_::_ = DROP j _`
                (mp_tac o Q.AP_TERM `LENGTH`) >>
              simp[LENGTH_DROP] >> decide_tac) >>
           qpat_x_assum `j = k` SUBST_ALL_TAC >> asm_rewrite_tac []) >>
        conj_tac >- (first_assum ACCEPT_TAC) >>
        conj_tac >-
          (gen_tac >> strip_tac >>
           qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ BodyStart _ _ _ _ _ _ /\ _`
             (qspec_then `H` mp_tac) >>
           (impl_tac >- (first_assum ACCEPT_TAC)) >>
           simp_tac (srw_ss()) [Abbr `BodyStart`, LET_THM] >>
           pure_once_rewrite_tac [GSYM evaluation_state_fupdcanon] >>
           simp_tac (srw_ss()) [storage_well_formed_on_def,
             vyperStorageBackendTheory.get_storage_def] >>
           strip_tac >> asm_rewrite_tac [] >>
           rpt gen_tac >> strip_tac >>
           qpat_assum `!b slot tv. MEM (b,slot,tv) _ ==> slots_in_range (get_storage cx (ee with <|scopes := _; gas_obs := _|>) b) _ _`
             (qspecl_then [`b`,`slot`,`tv`] mp_tac) >>
           Cases_on `b` >>
           simp_tac (srw_ss()) [vyperStorageBackendTheory.get_storage_def] >>
           disch_then irule >> first_assum ACCEPT_TAC) >>
        conj_tac >-
          (pure_once_rewrite_tac [GSYM evaluation_state_fupdcanon] >>
           first_assum ACCEPT_TAC) >>
        conj_tac >- (first_assum ACCEPT_TAC) >>
        conj_tac >- (first_assum ACCEPT_TAC) >>
        gen_tac >> strip_tac >>
        qpat_assum `!H. _ ==> BodyPost _ _ _ _ _ _ _ _ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- (first_assum ACCEPT_TAC)) >>
        simp_tac (srw_ss()) [Abbr `BodyPost`, LET_THM])) >>
     simp[]) >>
  `RoundObligation` by
    (simp_tac bool_ss [Abbr `RoundObligation`] >>
     rpt gen_tac >> strip_tac >>
     irule gas_outcome_full_initial_domain >>
     conj_tac >-
       (once_rewrite_tac[ignore_bind_def] >>
        irule storage_trace_frame_bind_all >>
        simp[storage_trace_frame_read_result] >> gen_tac >>
        once_rewrite_tac[ignore_bind_def] >>
        irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_ignore_bind,
          storage_trace_frame_state_updates, storage_trace_frame_finally,
          storage_trace_frame_pop_scope, storage_trace_frame_try,
          storage_trace_frame_return, storage_trace_frame_loop_handler,
          storage_trace_frame_read_result] >>
        irule storage_trace_frame_finally >>
        conj_tac >-
          (irule storage_trace_frame_try >>
           simp[storage_trace_frame_loop_handler] >>
           once_rewrite_tac[ignore_bind_def] >>
           irule storage_trace_frame_bind_all >>
           simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
        simp[storage_trace_frame_pop_scope]) >>
     conj_tac >- (first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!a rs ee s G tn. storage_trace_domain _ _ _ /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     qpat_x_assum `a = Value _` SUBST_ALL_TAC >>
     simp_tac bool_ss [read_result_def, bind_return] >>
     irule gas_outcome_full_zero_prefix_guarded >>
     conj_tac >-
       (once_rewrite_tac[ignore_bind_def] >>
        irule storage_trace_frame_bind_all >>
        simp[storage_trace_frame_state_updates] >>
        irule storage_trace_frame_finally >>
        simp[storage_trace_frame_pop_scope] >>
        irule storage_trace_frame_try >>
        simp[storage_trace_frame_loop_handler, storage_trace_frame_ignore_bind,
          evaluate_storage_trace_frame, storage_trace_frame_return]) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`Gstart`,`sstart`,`tnstart`] >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     irule (Q.INST [`B` |->
       `\H res mid G tn t. mid.gas_obs = [] /\
          BodyPost (sstart:venom_state) (Gstart:string |-> num # num)
            (tnstart:taint) H res mid G tn t`]
       for_handled_round_ptr_full) >>
     conj_tac >-
       (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ BodyStart _ _ _ _ _ _ /\ _`
          (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
        fs[Abbr `BodyStart`,storage_trace_domain_def]) >>
     qexistsl_tac [`BodyPost`,`Gstart`,`sstart`,`tnstart`] >>
     BETA_TAC >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `rs = DROP _ _` SUBST_ALL_TAC >>
        qpat_assum `ExitPostObligation` mp_tac >>
        simp_tac bool_ss [Abbr `ExitPostObligation`] >>
        disch_then irule >>
        `ee'.gas_obs = []` by
          (qpat_assum `!H. valid_horizon _ _ H ee'.storage_trace ==> _ /\ _`
             (qspec_then `storage_trace_horizon ee'.storage_trace` mp_tac) >>
           fs[storage_trace_domain_def]) >>
        asm_simp_tac bool_ss [] >>
        qexistsl_tac [`G`,`Gstart`,`ee`,`gs`,`s`,`sstart`,`tn`,`tnstart`] >>
        simp[] >>
        rpt strip_tac >> first_x_assum drule >> simp[]) >>
     simp_tac bool_ss [Abbr `BodyPost`] >>
     `BodyStart ee (IntV (n1 + &k))
        (storage_trace_horizon ee.storage_trace) sstart Gstart tnstart` by
       (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ BodyStart _ _ _ _ _ _ /\ _`
          (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
        fs[storage_trace_domain_def]) >>
     qpat_x_assum `BodyStart _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `BodyStart`,LET_THM] >> strip_tac >>
     `FLOOKUP cenv.ce_vars id = NONE` by
       (Cases_on `FLOOKUP cenv.ce_vars id` >- simp[] >>
        qpat_assum `ce_locals_declared _ _` mp_tac >>
        simp_tac bool_ss [ce_locals_declared_def] >>
        disch_then (qspecl_then [`id`,`x`] mp_tac) >> simp[]) >>
     `same_frame cenv bc` by
       (drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
        simp_tac bool_ss [same_frame_def] >> conj_tac >- asm_rewrite_tac[] >>
        qx_gen_tac `nm` >> Cases_on `nm = id` >-
          (pop_assum SUBST1_TAC >> simp[]) >>
        asm_simp_tac bool_ss []) >>
     `!H. dead_lo_ok H (DF H) lo bc cx` by
       (drule bodyPtrDefsTheory.same_frame_is_ctor >>
        fs[bodyPtrDefsTheory.dead_lo_ok_def]) >>
     irule for_full_body_fragment_normalized >>
     asm_simp_tac bool_ss [] >>
     conj_tac >-
       (`bc.ce_return_buf = cenv.ce_return_buf` by
          (qpat_assum `same_frame cenv bc` mp_tac >>
           simp_tac bool_ss [same_frame_def] >> strip_tac >>
           pop_assum kall_tac >>
           first_x_assum (mp_tac o Q.AP_TERM `\ce. ce.ce_return_buf`) >> simp[]) >>
        rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[] >>
        qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` irule >>
        qexists_tac `sz` >>
        qpat_assum `bc.ce_return_buf = cenv.ce_return_buf`
          (fn th => rewrite_tac[GSYM th]) >> asm_rewrite_tac[]) >>
     conj_tac >-
       (gen_tac >> simp_tac (srw_ss()) [] >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ lookup_var cv _ = _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- (first_assum ACCEPT_TAC)) >>
        simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
        pure_once_rewrite_tac [GSYM evaluation_state_fupdcanon] >>
        asm_simp_tac (srw_ss()) [exprLoweringPropsTheory.stmt_state_rel_start_gas_obs]) >>
     conj_tac >-
       (simp[block_is_terminated_def, mk_inst_def, is_terminator_def]) >>
     conj_tac >-
       (drule_all stmtSimPropsTheory.declare_local_reserved >> strip_tac >>
        irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
        qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[]) >>
     conj_tac >-
       (irule for_full_body_gas_admissible >>
        conj_tac >-
          (`expr_sim_inv cenv cx env ee` by
             (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> Inv _ _ _ _ _ _`
                (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
              simp_tac bool_ss [Abbr `Inv`] >>
              (impl_tac >-
                (qpat_assum `storage_trace_domain cx st0 ee.storage_trace` mp_tac >>
                 simp_tac bool_ss [storage_trace_domain_def])) >>
              strip_tac >> first_assum ACCEPT_TAC) >>
           qpat_x_assum `expr_sim_inv cenv cx env ee` mp_tac >>
           simp_tac bool_ss [expr_sim_inv_def,
             vyperTypeInvariantsTheory.env_consistent_def,
             vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
           strip_tac >>
           Cases_on `lookup_scopes id ee.scopes` >- simp[] >>
           qpat_x_assum `!nm entry. lookup_scopes nm ee.scopes = SOME entry ==> _`
             (drule_then mp_tac) >>
           asm_simp_tac (srw_ss()) [finite_mapTheory.FLOOKUP_DEF]) >>
        qexistsl_tac [`lctx`,`rs`] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ret_ty`,`shadow_func`,`shadow_body_in`,`shadow_body_out`,`stmts`] >>
     asm_simp_tac bool_ss [] >>
     irule for_full_body_fragment >>
     asm_simp_tac bool_ss [] >>
     conj_tac >-
       (qpat_assum `_ <> [] ==> body_stmts_full_ok cx stmts` irule >>
        pure_rewrite_tac [GENLIST_EQ_NIL] >> decide_tac) >>
     goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >>
     qexists_tac `bindings` >> qexists_tac `tops` >>
     asm_simp_tac bool_ss [] >>
     pure_once_rewrite_tac [GSYM evaluation_state_fupdcanon] >>
     asm_simp_tac (srw_ss()) [exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  qexistsl_tac
    [`\H res ee G tn t. res = INL () /\ Done H ee G tn t`,
     `\H res ee gt rr. ?ex. res = INR ex /\
       !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt rr`] >>
  conj_tac >- simp_tac bool_ss [Abbr `Done`] >>
  conj_tac >- simp_tac bool_ss [] >>
  irule (GEN_ALL (BETA_RULE (Q.INST
    [`R` |-> `\H ex ee gt rr. !tail.
      stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt rr`]
    (SPEC_ALL eval_for_rounds_full)))) >>
  conj_tac >-
    (qpat_assum `InitObligation` mp_tac >>
     simp_tac bool_ss [Abbr `InitObligation`, Abbr `Inv`] >>
     disch_then (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     (impl_tac >- (fs[storage_trace_domain_def])) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Inv`,
    `\rs b. if b then return () else eval_for cx tyv id stmts rs`,
    `stmt_res_ok lctx`,
    `\a. do v <- read_result cx a;
      push_scope_with_var id tyv v;
      finally (try (do eval_stmts cx stmts; return F od)
                   handle_loop_exception) pop_scope od`] >>
  BETA_TAC >>
  conj_tac >-
    (qpat_assum `RoundObligation` mp_tac >>
     simp_tac bool_ss [Abbr `RoundObligation`,Abbr `RoundPost`]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qmatch_asmsub_abbrev_tac `gas_marked_exec T _ roundop _ _ _ _ _` >>
     once_rewrite_tac [ignore_bind_def] >>
     once_rewrite_tac [bind_assoc] >>
     irule gasExemptCertTheory.gas_exempt_cert_bind_bool >>
     qexistsl_tac [`mid`,`t`,`b`] >>
     BETA_TAC >>
     qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac [ignore_bind_def] >> strip_tac >> asm_rewrite_tac []) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qmatch_asmsub_abbrev_tac `gas_exempt_cert T _ _ (ignore_bind roundop _) _ _ _ _` >>
     once_rewrite_tac [ignore_bind_def] >>
     once_rewrite_tac [bind_assoc] >>
     irule gasExemptCertTheory.gas_exempt_cert_error_bool >>
     asm_rewrite_tac []) >>
  simp_tac bool_ss [] >>
  conj_tac >-
    (qpat_assum `EmptyObligation` mp_tac >>
     simp_tac bool_ss [Abbr `EmptyObligation`]) >>
  conj_tac >-
    (qpat_assum `InitObligation` mp_tac >>
     simp_tac bool_ss [Abbr `InitObligation`]) >>
  asm_rewrite_tac []
QED

Resume body_for_range_lit_full[continuation]:
  `value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2)` by
    metis_tac[vyperTypeValuesTheory.well_typed_literal_sound,
              vyperValueOperationTheory.evaluate_literal_def] >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Gentry`,`ec`,`tnentry`] >>
  conj_tac >-
    (gen_tac >> irule (SRULE [APPEND_NIL] (Q.INST [`left` |-> `[]`, `right` |-> `[]`] (SPEC_ALL gas_origin_ptr_path_append))) >>
     qexistsl_tac [`G'`,`t`,`(OK t,G',tn')`,`tn'`] >>
     asm_rewrite_tac [APPEND_NIL] >>
     irule (SRULE [APPEND_NIL] (Q.INST [`left` |-> `[]`, `right` |-> `[]`] (SPEC_ALL gas_origin_ptr_path_append))) >>
     qexistsl_tac [`G'`,`e0`,`(OK e0,G',tn')`,`tn'`] >> asm_rewrite_tac [APPEND_NIL]) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  qexistsl_tac
    [`\H res ee G tn s. res = INL () /\
      stmt_lands lctx r (INL ()) s /\ ~s.vs_halted /\
      ~block_is_terminated r /\ cenv_top_ext cenv cenv ee.scopes /\
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv r s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
      (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP s.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))`,
     `\H res ee gt rr. ?ex. res = INR ex /\
       !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt rr`] >>
  conj_tac >- (rpt gen_tac >> simp_tac bool_ss [] >> strip_tac >> qexists_tac `cenv` >> asm_rewrite_tac []) >>
  conj_tac >- (simp_tac bool_ss [] >> rpt strip_tac >> asm_rewrite_tac []) >>
  mp_tac (Q.INST [`it` |-> `Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))`,
    `n` |-> `Num (n2-n1)`,
    `j1` |-> `sa.cs_next_id + 5`, `j2` |-> `sa.cs_next_id + 6`,
    `jstore` |-> `sa.cs_next_id + 7`] (SPEC_ALL for_range_continue_full)) >>
  (impl_tac >-
    (asm_rewrite_tac [] >>
     conj_tac >-
       (qspecl_then [`get_tenv cx`,`typ`,`tyv`] mp_tac range_end_words >>
        disch_then (qspecl_then [`n1`,`n2`] mp_tac) >> simp[]) >>
     conj_tac >-
       (Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
        metis_tac[ce_locals_declared_def]) >>
     conj_tac >-
       simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >>
     conj_tac >-
       simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >>
     conj_tac >-
       (rpt gen_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >> metis_tac[]) >>
     simp[ASCIInumbersTheory.toString_inj] >>
     conj_tac >-
       (irule lookup_block_fn_insts >>
        qpat_assum `lookup_block sa.cs_current_bb _ = _` (irule_at Any) >> simp[]) >>
     conj_tac >- metis_tac[compile_stmt_cs_mono,cs_mono_def] >>
     conj_tac >- metis_tac[compile_stmt_cs_mono,cs_mono_def] >>
     conj_tac >- simp[block_is_terminated_def] >>
     mp_tac (Q.INST [`sb` |-> `salloc`] (SPEC_ALL
       (BETA_RULE (PURE_REWRITE_RULE [LET_THM] for_range_literal_initial_inv)))) >>
     (impl_tac >-
       (simp[Abbr `e0`,Abbr `ec`] >> asm_rewrite_tac [] >>
        conj_tac >-
          (qspecl_then [`get_tenv cx`,`typ`,`tyv`] mp_tac range_end_words >>
           disch_then (qspecl_then [`n1`,`n2`] mp_tac) >> simp[]) >>
        conj_tac >- fs[ret_pc_ok_def] >>
        conj_tac >- metis_tac[] >>
        fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[])) >>
     disch_tac >> qx_gen_tac `H` >> disch_tac >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
       (qspec_then `H` mp_tac) >>
     simp[] >> strip_tac >> simp[] >>
     conj_tac >- metis_tac[] >>
     qpat_assum `lookup_var cv (update_var _ _ _) = _` mp_tac >>
     qpat_assum `lookup_var (STRING _ _) ec = SOME (i2w (n1 + _))` mp_tac >>
     qpat_x_assum `cv = _` (fn th => rewrite_tac [GSYM th]) >>
     simp[NoAsms,Abbr `ec`,jump_to_def,lookup_var_def])) >>
  simp[]
QED

Finalise body_for_range_lit_full

Theorem body_for_range_checked_full:
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (?e1 e2. it = Range e1 e2) /\
    ~(?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >> gvs[] >> rename1 `For id typ _ n stmts` >>
  `((case Range e1 e2 of
       Range (Literal _ (IntL n1)) (Literal _ (IntL n2)) =>
         n1 < n2 /\ n = Num (n2 - n1)
     | Range _ _ => 0 < n /\ well_typed_literal typ (IntL (&n))
     | Array e => expr_type e = ArrayT typ (Fixed n) \/
                  expr_type e = ArrayT typ (Dynamic n)) =
    (0 < n /\ well_typed_literal typ (IntL (&n))))` by
    (Cases_on `e1` >> gvs[] >>
     rename1 `Literal a lit` >> Cases_on `lit` >> gvs[] >>
     Cases_on `e2` >> gvs[] >>
     rename1 `Range _ (Literal a' lit')` >> Cases_on `lit'` >> gvs[]) >>
  `id NOTIN FDOM env.var_types /\ is_int_type typ /\
   well_typed_expr env e1 /\ well_typed_expr env e2 /\
   expr_type e1 = typ /\ expr_type e2 = typ /\
   well_formed_type env.type_defs typ /\ 0 < n /\
   well_typed_literal typ (IntL (&n)) /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    (gvs[type_stmt_def,well_typed_iterator_def,optionTheory.IS_SOME_EXISTS] >>
     metis_tac[assignable_type_well_formed]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def,optionTheory.IS_SOME_EXISTS] >>
  `body_iterator_full_ok cx (Range e1 e2)` by
    (first_x_assum irule >> simp[lift_option_type_def,return_def] >> metis_tac[]) >>
  `body_stmt_safe tops (For id typ (Range e1 e2) n stmts)` by
    metis_tac[supported_stmt_body_safe] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by (irule gasContextTheory.cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def,supported_stmt_expr_exists_def,
      supported_assignment_exists_def,supported_iterator_exists_def,
      supported_assert_exists_def,supported_raise_exists_def,
      supported_expr_exists_def,int_calls_stmt_def,int_calls_atarget_def,
      int_calls_iterator_def,int_calls_assert_reason_def,int_calls_raise_reason_def,
      listTheory.EVERY_APPEND,listTheory.EVERY_CONJ,
      DE_MORGAN_THM,GSYM expr_has_evm_run_def]) >>
  `~is_extcode e1 /\ ~is_extcode e2` by
    (fs[stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,
        allocLimitsTheory.alloc_limits_iterator_def] >>
     metis_tac[alloc_limits_expr_not_extcode]) >>
  `expr_body_pre cenv cx env e1 es` by
    (irule stmt_expr_body_pre_alloc >>
     gvs[stmt_exprs_ok_def,supported_stmt_expr_exists_def,
         supported_iterator_exists_def,int_calls_stmt_def,int_calls_iterator_def,
         allocLimitsTheory.alloc_limits_stmt_def,allocLimitsTheory.alloc_limits_iterator_def] >>
     qexists_tac `int_calls_expr e2 ++ int_calls_stmts stmts` >> simp[]) >>
  `!ei. expr_sim_inv cenv cx env ei ==> expr_body_pre cenv cx env e2 ei` by
    (rpt strip_tac >> irule stmt_expr_body_pre_alloc >>
     gvs[stmt_exprs_ok_def,supported_stmt_expr_exists_def,
         supported_iterator_exists_def,int_calls_stmt_def,int_calls_iterator_def,
         allocLimitsTheory.alloc_limits_stmt_def,allocLimitsTheory.alloc_limits_iterator_def] >>
     qexists_tac `int_calls_stmts stmts` >>
     metis_tac[call_evaluation_safe_append_right,listTheory.APPEND_ASSOC]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx typ e1 es` by
    (gvs[body_iterator_full_ok_def,body_expr_full_ok_def] >> metis_tac[]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (For _ _ _ _ _) sa = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,pairTheory.pair_case_eq] >>
  strip_tac >>
  Cases_on `compile_stmt cenv lctx ret_ty (For id typ (Range e1 e2) n stmts) sa` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) e1 sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e1) e1 sa = (op1,s1)` >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) e2 s1` >>
  rename1 `lower_value compile_expr cenv (expr_type e1) e2 s1 = (op2,s2)` >>
  `for_range_checked_code cenv lctx ret_ty id (expr_type e1) n stmts op1 op2 s2 = ((),r)` by
    metis_tac[compile_stmt_for_range_checked] >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa = (sop1,ss1)` >>
  `sop1 = op1 /\ gas_shadow_state s1 ss1` by
    (mp_tac (gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value
       |> Q.INST [`ty` |-> `expr_type e1`, `e` |-> `e1`]
       |> REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) ss1` >>
  rename1 `lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) ss1 = (sop2,ss2)` >>
  `sop2 = op2 /\ gas_shadow_state s2 ss2` by
    (mp_tac (gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value
       |> Q.INST [`ty` |-> `expr_type e1`, `e` |-> `e2`]
       |> REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`s1`,`ss1`] mp_tac) >> simp[]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends shadow_sa ss1 /\ cs_extends ss1 ss2` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `cs_extends s2 r` by
    (drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`)
       for_range_checked_parts >>
     disch_then (qspecl_then [`sa`,`func`] mp_tac) >>
     simp[] >>
     (impl_tac >-
       (conj_tac >- metis_tac[cs_extends_trans] >>
        rpt gen_tac >> strip_tac >>
        mp_tac (cj 2 compile_stmt_ci_mono) >>
        disch_then (qspecl_then [`c`,`lc`,`ret_ty`,`stmts`,`sa'`] mp_tac) >>
        simp[ci_mono_def])) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 r func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `!e a k. gas_shadow_expr e = Literal a (IntL k) <=> e = Literal a (IntL k)` by
    (Cases >> simp[gas_shadow_expr_def]) >>
  `compile_stmt cenv lctx ret_ty
    (For id (expr_type e1) (Range (gas_shadow_expr e1) (gas_shadow_expr e2))
       n (MAP gas_shadow_stmt stmts)) shadow_sa = ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_iterator_def,stmt_env_def,
          declare_stmt_local_def,comp_bind_def,comp_ignore_bind_def,
          comp_return_def,pairTheory.pair_case_eq] >>
     Cases_on `compile_stmt cenv lctx ret_ty
       (For id (expr_type e1) (Range (gas_shadow_expr e1) (gas_shadow_expr e2))
          n (MAP gas_shadow_stmt stmts)) shadow_sa` >>
     Cases_on `q` >> gvs[]) >>
  `for_range_checked_code cenv lctx ret_ty id (expr_type e1) n
     (MAP gas_shadow_stmt stmts) sop1 sop2 ss2 = ((),shadow_sb)` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
       (mp_then Any mp_tac compile_stmt_for_range_checked) >>
     disch_then drule >> simp[] >>
     disch_then (fn th => metis_tac[th])) >>
  `cs_extends ss2 shadow_sb` by
    (drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ ss2 = _`)
       for_range_checked_parts >>
     disch_then (qspecl_then [`shadow_sa`,`shadow_func`] mp_tac) >>
     simp[] >>
     (impl_tac >-
       (conj_tac >- metis_tac[cs_extends_trans] >>
        rpt gen_tac >> strip_tac >>
        mp_tac (cj 2 compile_stmt_ci_mono) >>
        disch_then (qspecl_then [`c`,`lc`,`ret_ty`,`MAP gas_shadow_stmt stmts`,`sa'`] mp_tac) >>
        simp[ci_mono_def])) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code shadow_sa ss1 shadow_func /\ fn_has_code ss1 ss2 shadow_func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  qabbrev_tac `prefix =
    do bc <- declare_local cenv id (expr_type e1);
       emit_local_alloca bc id;
       entry <- fresh_label "for_entry";
       cond <- fresh_label "for_cond";
       bod <- fresh_label "for_body";
       incr <- fresh_label "for_incr";
       exit <- fresh_label "for_exit";
       emit_inst JMP [Label entry] [];
       new_block entry;
       cv <- fresh_var;
       emit_inst ASSIGN [op1] [cv];
       rounds <- emit_op SUB [op2;op1];
       compile_range_bound_checks op1 op2 rounds n (is_signed_type (expr_type e1));
       ev <- emit_op ADD [op1;rounds];
       emit_inst JMP [Label cond] [];
       new_block cond;
       done <- emit_op EQ [Var cv;ev];
       emit_inst JNZ [done;Label exit;Label bod] [];
       new_block bod;
       (case FLOOKUP bc.ce_vars id of
          SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off);Var cv]
        | SOME (PtrVar ptr_op _) => emit_void MSTORE [ptr_op;Var cv]
        | _ => emit_void INVALID []);
       comp_return (bc,entry,cond,bod,incr,exit,cv,ev)
    od` >>
  `gas_shadow_compiles prefix prefix` by
    (simp[Abbr `prefix`,comp_ignore_bind_def] >>
     rpt (ho_match_mp_tac gasShadowStateTheory.gas_shadow_compiles_bind >> conj_tac
       >- simp[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_declare_local,
               gasShadowCompileStmtBaseTheory.gas_shadow_compiles_emit_local_alloca,
               gasShadowStateTheory.gas_shadow_compiles_fresh_label,
               gasShadowStateTheory.gas_shadow_compiles_fresh_var,
               gasShadowStateTheory.gas_shadow_compiles_emit_inst,
               gasShadowStateTheory.gas_shadow_compiles_new_block,
               gasShadowCompileStmtOpsTheory.gas_shadow_compiles_range_bound_checks,
               gasShadowStateTheory.gas_shadow_compiles_emit_op] >> gen_tac) >>
     ho_match_mp_tac gasShadowStateTheory.gas_shadow_compiles_bind >> conj_tac
     >- (Cases_on `FLOOKUP bc.ce_vars id` >>
         simp[gasShadowStateTheory.gas_shadow_compiles_emit_void] >>
         rename1 `SOME binding` >> Cases_on `binding` >>
         simp[gasShadowStateTheory.gas_shadow_compiles_emit_void]) >>
     gen_tac >> simp[gasShadowStateTheory.gas_shadow_compiles_return]) >>
  qabbrev_tac `suffix = \cv cond incr exit.
    do emit_jmp_if_not_terminated incr;
       new_block incr;
       nc <- emit_op ADD [Var cv;Lit 1w];
       emit_inst ASSIGN [nc] [cv];
       emit_inst JMP [Label cond] [];
       new_block exit;
       comp_return () od` >>
  `!bs. for_range_checked_code cenv lctx ret_ty id (expr_type e1) n bs op1 op2 =
    comp_bind prefix (\(bc,entry,cond,bod,incr,exit,cv,ev).
      comp_ignore_bind (compile_stmts bc (InLoop exit incr) ret_ty bs)
        (suffix cv cond incr exit))` by
    (gen_tac >> simp[for_range_checked_code_def,Abbr `prefix`,Abbr `suffix`,
       comp_ignore_bind_def,comp_bind_assoc,fragFuelTheory.comp_bind_return]) >>
  Cases_on `prefix s2` >> rename1 `prefix s2 = (packet,body_in)` >>
  PairCases_on `packet` >>
  rename1 `prefix s2 = ((pbc,pentry,pcond,pbod,pincr,pexit,pcv,pev),body_in)` >>
  Cases_on `prefix ss2` >> rename1 `prefix ss2 = (shadow_packet,shadow_body_in)` >>
  `shadow_packet = (pbc,pentry,pcond,pbod,pincr,pexit,pcv,pev) /\
   gas_shadow_state body_in shadow_body_in` by
    (qpat_assum `gas_shadow_compiles prefix prefix` mp_tac >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s2`,`ss2`] mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `shadow_packet = _` SUBST_ALL_TAC >>
  `!bs st. for_range_checked_code cenv lctx ret_ty id (expr_type e1) n bs op1 op2 st =
     comp_bind prefix (\(bc,entry,cond,bod,incr,exit,cv,ev).
       comp_ignore_bind (compile_stmts bc (InLoop exit incr) ret_ty bs)
         (suffix cv cond incr exit)) st` by simp[] >>
  `comp_ignore_bind (compile_stmts pbc (InLoop pexit pincr) ret_ty stmts)
     (suffix pcv pcond pincr pexit) body_in = ((),r)` by
    (qpat_assum `for_range_checked_code _ _ _ _ _ _ stmts _ _ s2 = _` mp_tac >>
     qpat_assum `!bs. for_range_checked_code _ _ _ _ _ _ _ _ _ = _`
       (fn th => rewrite_tac[th]) >>
     gvs[comp_bind_def]) >>
  `comp_ignore_bind (compile_stmts pbc (InLoop pexit pincr) ret_ty
     (MAP gas_shadow_stmt stmts)) (suffix pcv pcond pincr pexit) shadow_body_in =
       ((),shadow_sb)` by
    (qpat_assum `for_range_checked_code _ _ _ _ _ _ (MAP _ _) _ _ ss2 = _` mp_tac >>
     qpat_assum `!bs. for_range_checked_code _ _ _ _ _ _ _ _ _ = _`
       (fn th => rewrite_tac[th]) >>
     gvs[comp_bind_def]) >>
  Cases_on `stmts_env pbc (InLoop pexit pincr) ret_ty stmts body_in` >>
  rename1 `stmts_env pbc (InLoop pexit pincr) ret_ty stmts body_in = (pbc_out,body_out)` >>
  Cases_on `stmts_env pbc (InLoop pexit pincr) ret_ty (MAP gas_shadow_stmt stmts) shadow_body_in` >>
  rename1 `stmts_env pbc (InLoop pexit pincr) ret_ty (MAP gas_shadow_stmt stmts)
    shadow_body_in = (shadow_bc_out,shadow_body_out)` >>
  `shadow_bc_out = pbc_out /\ gas_shadow_state body_out shadow_body_out` by
    (mp_tac (Q.SPECL [`stmts`,`pbc`,`InLoop pexit pincr`,`ret_ty`] gas_shadow_stmts_env) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`body_in`,`shadow_body_in`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_bc_out = _` SUBST_ALL_TAC >>
  `compile_stmts pbc (InLoop pexit pincr) ret_ty stmts body_in = ((),body_out) /\
   compile_stmts pbc (InLoop pexit pincr) ret_ty (MAP gas_shadow_stmt stmts)
     shadow_body_in = ((),shadow_body_out)` by
    simp[stmtSimPropsTheory.compile_stmts_env] >>
  `suffix pcv pcond pincr pexit body_out = ((),r) /\
   suffix pcv pcond pincr pexit shadow_body_out = ((),shadow_sb)` by
    gvs[comp_ignore_bind_def,comp_bind_def] >>
  `cs_extends body_in body_out /\ cs_extends shadow_body_in shadow_body_out` by
    metis_tac[compile_stmt_cs_mono,cs_mono_def] >>
  `!st packet bs. prefix st = (packet,bs) ==> cs_extends st bs` by
    (rpt gen_tac >>
     simp[Abbr `prefix`,compile_range_bound_checks_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def,LET_THM] >>
     Cases_on `declare_local cenv id (expr_type e1) st` >>
     rename1 `_ = (bc,st1)` >>
     drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >> gvs[] >>
     Cases_on `is_signed_type (expr_type e1)` >>
     simp[emit_local_alloca_def,fresh_label_def,emit_inst_def,emit_op_def,
          emit_void_def,fresh_id_def,emit_def,new_block_def,fresh_var_def,
          comp_get_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM] >>
     strip_tac >> gvs[] >>
     simp[cs_extends_def] >> qexists_tac `[_;_;_]` >> simp[]) >>
  `cs_extends s2 body_in /\ cs_extends ss2 shadow_body_in` by metis_tac[] >>
  `!st u st'. suffix pcv pcond pincr pexit st = (u,st') ==> cs_extends st st'` by
    (rpt gen_tac >>
     simp[Abbr `suffix`,comp_ignore_bind_def,comp_bind_def] >>
     Cases_on `emit_jmp_if_not_terminated pincr st` >>
     rename1 `_ = (ju,jst)` >>
     `cs_extends st jst` by
       (qpat_x_assum `emit_jmp_if_not_terminated _ st = _` mp_tac >>
        simp[emit_jmp_if_not_terminated_def,comp_get_def,comp_bind_def] >>
        Cases_on `block_is_terminated st` >>
        simp[comp_return_def,cs_extends_refl] >>
        metis_tac[cs_extends_emit_inst]) >>
     simp[new_block_def,emit_op_def,emit_inst_def,fresh_var_def,fresh_id_def,
          emit_def,comp_bind_def,comp_return_def,comp_ignore_bind_def,LET_THM] >>
     strip_tac >> gvs[] >>
     irule cs_extends_trans >> qexists_tac `jst` >> simp[] >>
     simp[cs_extends_def] >> qexists_tac `[_;_]` >> simp[]) >>
  `cs_extends body_out r /\ cs_extends shadow_body_out shadow_sb` by metis_tac[] >>
  `fn_has_code body_in body_out func /\
   fn_has_code shadow_body_in shadow_body_out shadow_func` by
    metis_tac[fn_has_code_mid,cs_extends_trans] >>
  `declare_local cenv id (expr_type e1) s2 =
     (pbc,s2 with cs_next_var := s2.cs_next_var + 1) /\
   pentry = fresh_label_output "for_entry" s2.cs_next_label /\
   pcond = fresh_label_output "for_cond" (s2.cs_next_label + 1) /\
   pbod = fresh_label_output "for_body" (s2.cs_next_label + 2) /\
   pincr = fresh_label_output "for_incr" (s2.cs_next_label + 3) /\
   pexit = fresh_label_output "for_exit" (s2.cs_next_label + 4) /\
   pcv = STRING #"%" (toString (s2.cs_next_var + 1)) /\
   pev = Var (STRING #"%" (toString (s2.cs_next_var + 7))) /\
   body_in.cs_current_bb = pbod /\
   body_in.cs_current_insts =
     [mk_inst (s2.cs_next_id + 14) MSTORE
       [Var (STRING #"%" (toString s2.cs_next_var));Var pcv] []] /\
   body_in.cs_next_var = s2.cs_next_var + 9 /\
   s2.cs_next_id <= body_in.cs_next_id` by
    (qpat_assum `prefix s2 = _` mp_tac >>
     qpat_assum `Abbrev (prefix = _)` mp_tac >>
     qpat_assum `cenv.ce_alloca_locals` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
     Cases_on `declare_local cenv id (expr_type e1) s2` >>
     rename1 `declare_local cenv id (expr_type e1) s2 = (bc,ds)` >>
     drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     qpat_x_assum `prefix s2 = _` mp_tac >>
     Cases_on `is_signed_type (expr_type e1)` >>
     simp[Abbr `prefix`,compile_range_bound_checks_def,
          emit_local_alloca_def,fresh_label_def,emit_inst_def,emit_op_def,
          emit_void_def,fresh_id_def,emit_def,new_block_def,fresh_var_def,
          comp_get_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM] >>
     gvs[] >> rpt strip_tac >> gvs[]) >>
  Cases_on `emit_jmp_if_not_terminated pincr body_out` >>
  rename1 `emit_jmp_if_not_terminated pincr body_out = (pju,pj)` >>
  `pj.cs_next_var = body_out.cs_next_var /\
   cs_extends body_out pj /\
   (~block_is_terminated body_out ==>
     pj.cs_blocks = body_out.cs_blocks /\
     pj.cs_current_bb = body_out.cs_current_bb /\
     pj.cs_current_insts = body_out.cs_current_insts ++
       [mk_inst body_out.cs_next_id JMP [Label pincr] []])` by
    (qpat_assum `emit_jmp_if_not_terminated pincr body_out = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[emit_jmp_if_not_terminated_def,comp_get_def,comp_bind_def] >>
     Cases_on `block_is_terminated body_out` >>
     simp[comp_return_def,cs_extends_refl,emit_inst_def,fresh_id_def,
          emit_def,comp_bind_def,comp_return_def,LET_THM] >>
     strip_tac >> gvs[cs_extends_def]) >>
  `cs_extends pj r` by
    (qpat_assum `suffix pcv pcond pincr pexit body_out = _` mp_tac >>
     qpat_assum `Abbrev (suffix = _)` mp_tac >>
     qpat_assum `emit_jmp_if_not_terminated pincr body_out = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
     qpat_x_assum `suffix pcv pcond pincr pexit body_out = _` mp_tac >>
     simp[Abbr `suffix`,comp_bind_def,comp_ignore_bind_def] >>
     simp[new_block_def,emit_op_def,emit_inst_def,fresh_var_def,fresh_id_def,
          emit_def,comp_bind_def,comp_return_def,comp_ignore_bind_def,LET_THM] >>
     strip_tac >> gvs[] >> simp[cs_extends_def] >>
     qexists_tac `[_;_]` >> simp[]) >>
  `fn_has_code body_out r func` by
    (irule fn_has_code_mid >> conj_tac >- simp[] >>
     qexistsl_tac [`r`,`s2`] >> simp[cs_extends_refl] >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code body_out pj func /\ fn_has_code pj r func` by
    (conj_tac >> irule fn_has_code_mid >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`r`,`body_out`] >> simp[cs_extends_refl]) >>
  `lookup_block pincr func.fn_blocks = SOME
     <|bb_label := pincr; bb_instructions :=
       [mk_inst pj.cs_next_id ADD [Var pcv;Lit 1w]
          [STRING #"%" (toString pj.cs_next_var)];
        mk_inst (pj.cs_next_id + 1) ASSIGN
          [Var (STRING #"%" (toString pj.cs_next_var))] [pcv];
        mk_inst (pj.cs_next_id + 2) JMP [Label pcond] []]|>` by
    (qpat_assum `suffix pcv pcond pincr pexit body_out = _` mp_tac >>
     qpat_assum `Abbrev (suffix = _)` mp_tac >>
     qpat_assum `emit_jmp_if_not_terminated pincr body_out = _` mp_tac >>
     qpat_assum `fn_has_code pj r func` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 disch_tac >>
     qpat_x_assum `suffix pcv pcond pincr pexit body_out = _` mp_tac >>
     simp[Abbr `suffix`,new_block_def,emit_op_def,emit_inst_def,
          fresh_var_def,fresh_id_def,emit_def,comp_bind_def,
          comp_return_def,comp_ignore_bind_def,LET_THM] >>
     strip_tac >> gvs[fn_has_code_def,emitted_blocks_def] >>
     qmatch_goalsub_abbrev_tac `SOME ib` >>
     qpat_x_assum `!bb'. _` (qspec_then `ib` mp_tac) >>
     simp[Abbr `ib`]) >>

  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  gvs[] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (fn th => drule_all (REWRITE_RULE [expr_sim_full_def] th)) >>
  disch_tac >>
  `eval_iterator cx (Range e1 e2) =
   do v1 <- bind (eval_expr cx e1) (read_result cx);
      v2 <- bind (eval_expr cx e2) (read_result cx);
      rl <- lift_sum (get_range_limits v1 v2);
      return (MAP Value (GENLIST (\j. IntV (FST rl + &j)) (SND rl))) od` by
    (simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
     qx_gen_tac `ei` >> Cases_on `eval_expr cx e1 ei` >>
     rename1 `_ = (raw1, es1)` >> Cases_on `raw1` >> simp[] >>
     rename1 `read_result cx tv1 es1` >>
     Cases_on `read_result cx tv1 es1` >> rename1 `_ = (r1, es2)` >>
     Cases_on `r1` >> simp[] >>
     Cases_on `eval_expr cx e2 es2` >> rename1 `_ = (raw2, es3)` >>
     Cases_on `raw2` >> simp[] >>
     rename1 `read_result cx tv2 es3` >>
     Cases_on `read_result cx tv2 es3` >> rename1 `_ = (r2, es4)` >>
     Cases_on `r2` >> simp[MAP_GENLIST, combinTheory.o_DEF]) >>
  `eval_stmt cx (For id (expr_type e1) (Range e1 e2) n stmts) =
   do v1 <- bind (eval_expr cx e1) (read_result cx);
      v2 <- bind (eval_expr cx e2) (read_result cx);
      rl <- lift_sum (get_range_limits v1 v2);
      check (compatible_bound (Dynamic n) (SND rl)) "For too long";
      eval_for cx tyv id stmts
        (MAP Value (GENLIST (\j. IntV (FST rl + &j)) (SND rl))) od` by
    (pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, lift_option_type_def, bind_assoc, bind_return, LENGTH_GENLIST]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ firstQ firstR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> MATCH_MP_TAC storage_trace_frame_bind_all >>
      conj_tac
      >- (MATCH_MP_TAC storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> MATCH_MP_TAC storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >>
      MATCH_MP_TAC storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks, evaluate_storage_trace_frame]) >>
  qexists_tac `\H res ee G tn t. firstQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected_first" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `firstR`] >> rpt strip_tac >>
  Cases_on `res` >- (qpat_x_assum `expr_exit (INL _) _` mp_tac >> simp[exprSimDefsTheory.expr_exit_def]) >>
  simp[stmt_exit_ptr_def] >> gen_tac >> disj1_tac >>
  qpat_x_assum `expr_exit (INR _) _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume body_for_range_checked_full[selected_first]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qunabbrev_tac `firstQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by
       fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL v`, `mid with gas_obs := []`] mp_tac) >>
     (impl_tac >-
       (qpat_x_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >>
        simp[NoAsms, bind_def])) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by metis_tac[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e2 mid` by
    (`?ei raw em ej vv en. eval_expr cx e1 ei = (INL raw,em) /\
        read_result cx raw ej = (INL vv,en)` by
       (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
          (qspec_then `[]` mp_tac) >>
        simp[NoAsms,bind_def,AllCaseEqs()] >> metis_tac[]) >>
     qpat_x_assum `body_iterator_full_ok _ _`
       (mp_tac o REWRITE_RULE [body_iterator_full_ok_def,body_expr_full_ok_def]) >>
     simp[] >> strip_tac >>
     qpat_x_assum `(?s tv t s1 v t1. _) ==> _` mp_tac >>
     (impl_tac >- metis_tac[]) >> strip_tac >>
     qpat_x_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full _ _ _ _ e2 _ /\ _` (irule o cj 1) >>
     metis_tac[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv s1 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[expr_post_def]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid t /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 mid`
    (fn th => drule_all (REWRITE_RULE [expr_sim_full_def] th)) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _
    (bind (eval_expr cx e2) (read_result cx)) _ secondQ secondR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t'`, `v'`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> MATCH_MP_TAC storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >>
      MATCH_MP_TAC storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks, evaluate_storage_trace_frame]) >>
  qexists_tac `\H res ee G tn t. secondQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected_second" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ secondQ secondR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `secondR`] >> rpt strip_tac >>
  Cases_on `res` >- (qpat_x_assum `expr_exit (INL _) _` mp_tac >> simp[exprSimDefsTheory.expr_exit_def]) >>
  simp[stmt_exit_ptr_def] >> gen_tac >> disj1_tac >>
  qpat_x_assum `expr_exit (INR _) _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume body_for_range_checked_full[selected_second]:
  qx_genl_tac [`marks2`, `res2`, `ee`, `G2`, `tn2`, `t2`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qunabbrev_tac `secondQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res2 = INL _` SUBST_ALL_TAC >>
  qexists_tac `v'` >> simp[] >>
  `expr_result_typed env e1 (Value v)` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by
       fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL v`, `mid with gas_obs := []`] mp_tac) >>
     (impl_tac >-
       (qpat_x_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >>
        simp[NoAsms, bind_def])) >> simp[]) >>
  `expr_result_typed env e2 (Value v')` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e2
        (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings ++ [])` by
       fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL v'`, `ee with gas_obs := []`] mp_tac) >>
     (impl_tac >-
       (qpat_x_assum `bind (eval_expr cx e2) _ _ = _` mp_tac >>
        simp[NoAsms, bind_def])) >> simp[]) >>
  `value_has_type tyv v /\ value_has_type tyv v'` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def, value_result_typed_def] >>
  `?n1. v = IntV n1 /\ value_has_type tyv (IntV n1)` by
    (qspecl_then [`get_tenv cx`, `expr_type e1`, `tyv`, `v`]
       mp_tac exprSimBinopFragTheory.int_type_value >>
     (impl_tac >- simp[]) >> strip_tac >> gvs[]) >>
  `?n2. v' = IntV n2 /\ value_has_type tyv (IntV n2)` by
    (qspecl_then [`get_tenv cx`, `expr_type e1`, `tyv`, `v'`]
       mp_tac exprSimBinopFragTheory.int_type_value >>
     (impl_tac >- simp[]) >> strip_tac >> gvs[]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  qpat_x_assum `v' = IntV _` SUBST_ALL_TAC >>
  `for_range_checked_code cenv lctx ret_ty id (expr_type e1) n stmts op1 op2 s2 = ((),r)` by
    asm_rewrite_tac [] >>
  qpat_assum `for_range_checked_code _ _ _ _ _ _ stmts _ _ s2 = _`
    (mp_then Any mp_tac for_range_checked_parts) >>
  disch_then (qspecl_then [`s2`,`func`] mp_tac) >>
  (impl_tac >-
    (simp[cs_extends_refl] >> rpt gen_tac >> strip_tac >>
     mp_tac (cj 2 compile_stmt_ci_mono) >>
     disch_then (qspecl_then [`c`,`lc`,`ret_ty`,`stmts`,`sa'`] mp_tac) >>
     simp[ci_mono_def])) >> strip_tac >>
  qpat_x_assum `lookup_block _ _ = SOME <|bb_label := _; bb_instructions :=
    [mk_inst sj.cs_next_id ADD _ _; _; _]|>` kall_tac >>
  `type_memory_bytes cenv (expr_type e1) = 32` by
    (qpat_assum `is_int_type (expr_type e1)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `expr_type e1` >> simp[is_int_type_def] >>
     Cases_on `b` >> simp[is_int_type_def,type_memory_bytes_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
     ctx func cenv cx ee t2` by fs[expr_post_def] >>
  `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by
    fs[ghost_inv_at_def] >>
  `s1.cs_next_var <= s2.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e2 s1 = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  qabbrev_tac `salloc = s2 with <|
    cs_next_var := s2.cs_next_var + 1;
    cs_next_id := s2.cs_next_id + 1;
    cs_current_insts := s2.cs_current_insts ++
      [mk_inst s2.cs_next_id ALLOCA [Lit 32w] [p]] |>` >>
  `compile_alloc_buffer 32 s2 =
    (<|buf_operand := Var p; buf_size := 32|>,salloc)` by
    (simp[compile_alloc_buffer_def,emit_op_def,fresh_var_def,
          emit_inst_def,fresh_id_def,emit_def,comp_bind_def,
          comp_return_def,comp_ignore_bind_def,Abbr `salloc`] >> gvs[]) >>
  `fn_has_code s2 salloc func` by
    (simp[fn_has_code_def,emitted_blocks_def,Abbr `salloc`] >>
     qexists_tac `<|bb_label := s2.cs_current_bb;
       bb_instructions := s2.cs_current_insts ++
         [mk_inst s2.cs_next_id ALLOCA [Lit 32w] [p];
          mk_inst (s2.cs_next_id + 1) JMP [Label entry_lbl] []]|>` >>
     simp[]) >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tn2`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G2`]
    strip_assume_tac) >>
  fs[buffer_accessors,operand_11] >>
  `~t'.vs_halted` by
    (qpat_assum `t' with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|> = t2` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >>
     simp[]) >>
  `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t',G',tn') [] (OK (jump_to entry_lbl t'),G',tn')` by
    (gen_tac >> irule jmp_origin_ptr_path >>
     fs[Abbr `salloc`] >> simp[get_instruction_def,EL_APPEND_EQN] >>
     qexists_tac `s2.cs_next_id + 1` >> simp[]) >>
  qabbrev_tac `e0 = jump_to entry_lbl t'` >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    (simp[] >> qpat_assum `is_int_type _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `expr_type e1` >> simp[is_int_type_def,is_word_type_def] >>
     Cases_on `b` >> simp[is_int_type_def,is_word_type_def]) >>
  `eval_operand op1 t = SOME (i2w n1)` by
    (qpat_assum `evaluate_type _ (expr_type e1) = SOME _` mp_tac >>
     qpat_assum `is_word_type (expr_type e1)` mp_tac >>
     qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[expr_post_def,expr_val_rel_def] >> rpt strip_tac >>
     gvs[] >>
     simp[exprSimPropsTheory.typed_val_to_w256_word_value,
          loweringSliceTheory.word_value_def,valueEncodingTheory.val_to_w256_def]) >>
  `eval_operand op2 t2 = SOME (i2w n2)` by
    (qpat_assum `evaluate_type _ (expr_type e1) = SOME _` mp_tac >>
     qpat_assum `expr_type e2 = expr_type e1` mp_tac >>
     qpat_assum `is_word_type (expr_type e2)` mp_tac >>
     qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[expr_post_def,expr_val_rel_def] >> rpt strip_tac >>
     gvs[] >>
     simp[exprSimPropsTheory.typed_val_to_w256_word_value,
          loweringSliceTheory.word_value_def,valueEncodingTheory.val_to_w256_def]) >>
  `!x. op1 = Var x ==> not_fresh_at s1 x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!x. op2 = Var x ==> not_fresh_at s2 x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `(!l. op1 <> Label l) /\ (!l. op2 <> Label l)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
  `eval_operand op1 t2 = SOME (i2w n1)` by
    (qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
     qpat_assum `eval_operand op1 t = _` mp_tac >>
     qpat_assum `!l. op1 <> Label l` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[expr_post_def] >> rpt strip_tac >>
     Cases_on `op1` >> fs[eval_operand_def]) >>
  `eval_operand op1 e0 = SOME (i2w n1) /\
   eval_operand op2 e0 = SOME (i2w n2)` by
    (simp[Abbr `e0`,jump_to_def] >>
     qpat_assum `!x. not_fresh_at s2 x ==> _` mp_tac >>
     qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
     qpat_assum `!x. op2 = Var x ==> _` mp_tac >>
     qpat_assum `!l. op1 <> Label l` mp_tac >>
     qpat_assum `!l. op2 <> Label l` mp_tac >>
     qpat_assum `eval_operand op1 t2 = _` mp_tac >>
     qpat_assum `eval_operand op2 t2 = _` mp_tac >>
     qpat_assum `s1.cs_next_var <= s2.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexists_tac `s2` >> qexists_tac `t2` >>
     simp[lookup_var_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `op_prov G1 op1 = NONE /\ op_taint tn1 op1 = {} /\
   op_prov G2 op2 = NONE /\ op_taint tn2 op2 = {}` by
    fs[ptr_val_ok_def] >>
  `op_prov G2 op1 = NONE /\ op_taint tn2 op1 = {}` by
    (qpat_assum `ghost_kept_at lo cenv mid s1 _ _ _ _ _` mp_tac >>
     qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
     qpat_assum `!l. op1 <> Label l` mp_tac >>
     qpat_assum `op_prov G1 op1 = NONE` mp_tac >>
     qpat_assum `op_taint tn1 op1 = {}` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[ghost_kept_at_def] >> rpt strip_tac >>
     Cases_on `op1` >> fs[op_prov_def,op_taint_def]) >>
  `op_prov G' op1 = NONE /\ op_taint tn' op1 = {} /\
   op_prov G' op2 = NONE /\ op_taint tn' op2 = {}` by
    (qpat_assum `!x. not_fresh_at s2 x ==> _` mp_tac >>
     qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
     qpat_assum `!x. op2 = Var x ==> _` mp_tac >>
     qpat_assum `!l. op1 <> Label l` mp_tac >>
     qpat_assum `!l. op2 <> Label l` mp_tac >>
     qpat_assum `op_prov G2 op1 = NONE` mp_tac >>
     qpat_assum `op_taint tn2 op1 = {}` mp_tac >>
     qpat_assum `op_prov G2 op2 = NONE` mp_tac >>
     qpat_assum `op_taint tn2 op2 = {}` mp_tac >>
     qpat_assum `s1.cs_next_var <= s2.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `op1` >> Cases_on `op2` >>
     fs[op_prov_def,op_taint_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev]` by
    simp[ASCIInumbersTheory.toString_inj] >>
  `!x. op1 = Var x \/ op2 = Var x ==>
     ~MEM x [cv;rv;g1;z1;g2;z2;ev]` by
    (qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
     qpat_assum `!x. op2 = Var x ==> _` mp_tac >>
     qpat_assum `s1.cs_next_var <= s2.cs_next_var` mp_tac >>
     map_every (fn v => qpat_assum v mp_tac)
       [`cv = _`,`rv = _`,`g1 = _`,`z1 = _`,`g2 = _`,`z2 = _`,`ev = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS,arithmeticTheory.LE_ADD]) >>
  `e0.vs_current_bb = entry_lbl /\ e0.vs_inst_idx = 0 /\
   ~e0.vs_halted /\ allocas_from lo e0` by
    (qpat_assum `Abbrev (e0 = _)` mp_tac >>
     qpat_assum `allocas_from lo t'` mp_tac >>
     qpat_assum `~t'.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[markerTheory.Abbrev_def] >> rpt strip_tac >>
     gvs[jump_to_def,allocas_from_def] >> metis_tac[]) >>
  `((if is_signed_type (expr_type e1) then
       word_gt (i2w n1 : bytes32) (i2w n2)
     else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1) /\
   (n1 <= n2 ==> Num (n2-n1) < dimword (:256) /\
     w2n (i2w n2 - i2w n1 : bytes32) = Num (n2-n1))` by
    (qspecl_then [`get_tenv cx`,`expr_type e1`,`tyv`,`n1`,`n2`]
       mp_tac range_end_words >> simp[]) >>
  qabbrev_tac `cmp = if is_signed_type (expr_type e1) then SGT else GT` >>
  qabbrev_tac `bad1 = (n2 < n1)` >>
  qabbrev_tac `bad2 = (w2n (i2w n2 - i2w n1 : bytes32) >
    w2n (n2w n : bytes32))` >>
  qabbrev_tac `code = [mk_inst (s2.cs_next_id+2) ASSIGN [op1] [cv];
    mk_inst (s2.cs_next_id+3) SUB [op2;op1] [rv];
    mk_inst (s2.cs_next_id+4) cmp [op1;op2] [g1];
    mk_inst (s2.cs_next_id+5) ISZERO [Var g1] [z1];
    mk_inst (s2.cs_next_id+6) ASSERT [Var z1] [];
    mk_inst (s2.cs_next_id+7) GT [Var rv;Lit (n2w n)] [g2];
    mk_inst (s2.cs_next_id+8) ISZERO [Var g2] [z2];
    mk_inst (s2.cs_next_id+9) ASSERT [Var z2] [];
    mk_inst (s2.cs_next_id+10) ADD [op1;Var rv] [ev]]` >>
  qabbrev_tac `k = if bad1 then 4 else if bad2 then 7 else 9` >>
  qabbrev_tac `ws = if bad1 then [cv;rv;g1;z1]
    else if bad2 then [cv;rv;g1;z1;g2;z2]
    else [cv;rv;g1;z1;g2;z2;ev]` >>
  qabbrev_tac `Gc = DRESTRICT G' (COMPL (set ws))` >>
  qabbrev_tac `tc = tn' with t_var := tn'.t_var |++ MAP (\v. (v,{})) ws` >>
  `(!D lo'. allocas_from lo' e0 /\ lo' <= e0.vs_alloca_next ==>
      inst_seq_ptr D lo' ctx func PG G' tn' (TAKE k code) e0 Gc tc) /\
   ((bad1 \/ bad2) ==> op_taint tc (Var (if bad1 then z1 else z2)) = {})` by
    (irule for_checked_entry_ghost_packet >> simp[Abbr `k`] >>
     qexistsl_tac [`i2w n1`,`i2w n2`,`n`,`cmp`,`cv`,`ev`,`g1`,`g2`,
                   `s2.cs_next_id+2`,`op1`,`op2`,`rv`] >>
     simp[Abbr `code`,Abbr `ws`,Abbr `Gc`,Abbr `tc`,
          Abbr `bad1`,Abbr `bad2`,Abbr `cmp`,arithmeticTheory.ADD_ASSOC] >>
     qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> ~MEM x _` mp_tac >>
     Cases_on `is_signed_type (expr_type e1)` >>
     fs[] >> rpt strip_tac >> simp[]) >>
  qabbrev_tac `u1 = update_var cv (i2w n1) e0` >>
  qabbrev_tac `u2 = update_var rv (i2w n2 - i2w n1) u1` >>
  qabbrev_tac `u3 = update_var g1 (bool_to_word bad1) u2` >>
  qabbrev_tac `u4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) u3` >>
  qabbrev_tac `u5 = update_var g2 (bool_to_word bad2) u4` >>
  qabbrev_tac `u6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) u5` >>
  qabbrev_tac `u7 = update_var ev (i2w n1 + (i2w n2 - i2w n1)) u6` >>
  `bad1 \/ bad2 ==>
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (e0,G',tn') []
        (Abort Revert_abort (revert_state (set_returndata []
          ((if bad1 then u4 else u6) with vs_inst_idx := k))),Gc,tc)` by
    (disch_tac >> gen_tac >> disch_tac >>
     qpat_assum `Abbrev (code = _)`
       (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     disch_then (mp_tac o MATCH_MP for_range_checked_reject_path_from_code) >>
     disch_then irule >>
     simp[] >>
     (conj_tac >-
       (qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> ~MEM x _`
          mp_tac >> simp[])) >>
     (conj_tac >-
       (qmatch_asmsub_abbrev_tac `lookup_block entry_lbl _ = SOME ebb` >>
        qexistsl_tac [`ebb`,`[mk_inst (s2.cs_next_id+11) JMP [Label cond_lbl] []]`] >>
        qpat_x_assum `lookup_block entry_lbl _ = SOME ebb` mp_tac >>
        simp[Abbr `ebb`,Abbr `code`,Abbr `cmp`,arithmeticTheory.ADD_ASSOC])) >>
     simp[Abbr `cmp`,Abbr `bad1`,Abbr `bad2`,Abbr `k`,
          Abbr `u1`,Abbr `u2`,Abbr `u3`,Abbr `u4`,
          Abbr `u5`,Abbr `u6`] >>
     (conj_tac >-
       (Cases_on `is_signed_type (expr_type e1)` >> simp[])) >>
     (conj_tac >-
       (qpat_assum `z1 = _` mp_tac >>
        qpat_assum `z2 = _` mp_tac >>
        qpat_assum `(if is_signed_type _ then _ else _) <=> _` mp_tac >>
        qpat_assum `n2 < n1 \/ _` mp_tac >>
        qpat_assum `_ ==> op_taint tc _ = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `is_signed_type (expr_type e1)` >>
        simp[] >> rpt strip_tac >> gvs[])) >>
     qexistsl_tac [`cx`,`ee`,`st0`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!D lo'. _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[] >> disch_then irule >> simp[] >>
     simp[Abbr `e0`,jump_to_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `value_has_type tyv (IntV (&n))` by
    (drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  `value_has_type tyv (IntV 0)` by
    (qpat_assum `is_int_type (expr_type e1)` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e1) = SOME tyv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `expr_type e1` >> gvs[is_int_type_def] >>
     rename1 `evaluate_type _ (BaseT bt) = _` >> Cases_on `bt` >>
     gvs[is_int_type_def, vyperValueTheory.evaluate_type_def,
         vyperTypingTheory.value_has_type_def, vyperValueTheory.within_int_bound_def]) >>
  `n < dimword (:256)` by
    (drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
     disch_then (qspecl_then [`0`, `&n`] mp_tac) >> simp[]) >>
  Cases_on `bad1 \/ bad2`
  >- (irule gas_outcome_full_exit >>
      (conj_tac >- (qexistsl_tac [`Gc`,`ee`,
        `Abort Revert_abort (revert_state (set_returndata []
          ((if bad1 then u4 else u6) with vs_inst_idx := k)))`,
        `if bad1 then INR (Error (RuntimeError "no range"))
         else INR (Error (RuntimeError "For too long"))`,`tc`] >>
      simp[fragExecTheory.exit_result_def] >>
      (conj_tac >-
        (qunabbrev_tac `bad1` >> qunabbrev_tac `bad2` >>
         Cases_on `n2 < n1` >>
         fs[GSYM integerTheory.INT_NOT_LE,get_range_limits_def,
            lift_sum_def,bind_def,ignore_bind_def,return_def,raise_def,
            check_def,assert_def,compatible_bound_def] >>
         `~(Num (n2 - n1) <= n)` by
           (qpat_assum `w2n _ > _` mp_tac >>
            qpat_assum `w2n _ = Num (n2 - n1)` (fn th => rewrite_tac[th]) >>
            `n MOD dimword (:256) = n` by simp[arithmeticTheory.LESS_MOD] >>
            simp[] >> decide_tac) >> simp[])) >>
      gen_tac >> disch_tac >>
      (reverse conj_tac >-
        (Cases_on `bad1` >> simp[stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def])) >>
      irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`G'`,`e0`,`tn'`] >>
      (reverse conj_tac >- metis_tac[]) >>
      irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`G'`,`t'`,`tn'`] >>
      simp[])) >> simp[]) >>
  `~bad1 /\ ~bad2` by metis_tac[] >>
  `n1 <= n2` by
    (qpat_assum `~bad1` mp_tac >> simp[Abbr `bad1`,integerTheory.INT_NOT_LT]) >>
  `Num (n2-n1) <= n` by
    (qpat_assum `n1 <= n2 ==> _` drule >> strip_tac >>
     `n MOD dimword (:256) = n` by metis_tac[arithmeticTheory.LESS_MOD] >>
     qpat_assum `~bad2` mp_tac >>
     qunabbrev_tac `bad2` >>
     qpat_assum `w2n (i2w n2 - i2w n1) = _` (fn th => rewrite_tac[th]) >>
     simp[] >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (e0,G',tn') [] (OK (jump_to cond_lbl u7),Gc,tc)` by
    (gen_tac >> disch_tac >>
     qpat_assum `Abbrev (code = _)`
       (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     disch_then (mp_tac o MATCH_MP for_range_checked_entry_path_from_code) >>
     disch_then irule >> simp[] >>
     (conj_tac >-
       (qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> ~MEM x _`
          mp_tac >> simp[])) >>
     (conj_tac >-
       (qpat_assum `lookup_block entry_lbl _ = SOME _` mp_tac >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`Abbrev (code = _)`,`Abbrev (cmp = _)`,
           `entry_lbl = _`,`cond_lbl = _`,`cv = _`,`rv = _`,`g1 = _`,
           `z1 = _`,`g2 = _`,`z2 = _`,`ev = _`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[markerTheory.Abbrev_def,arithmeticTheory.ADD_ASSOC])) >>
     simp[Abbr `cmp`,Abbr `bad1`,Abbr `bad2`,
          Abbr `u1`,Abbr `u2`,Abbr `u3`,Abbr `u4`,
          Abbr `u5`,Abbr `u6`,Abbr `u7`] >>
     Cases_on `is_signed_type (expr_type e1)` >> fs[] >>
     qexistsl_tac [`cx`,`ee`,`st0`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!D lo'. _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `k`,Abbr `code`] >> disch_then irule >> simp[] >>
     simp[Abbr `e0`,jump_to_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e2
        (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings ++ [])` by
       fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL (IntV n2)`, `ee with gas_obs := []`] mp_tac) >>
     (impl_tac >-
       (qpat_x_assum `bind (eval_expr cx e2) _ _ = _` mp_tac >>
        simp[NoAsms,bind_def])) >> simp[]) >>
  `return_buf_frame d cenv s2 t2` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`t`,`s1`] >> fs[expr_post_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee t2 /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 t2` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> fs[expr_post_def]) >>
  qabbrev_tac `ec = jump_to cond_lbl u7` >>
  `!x. not_fresh_at s2 x ==>
     ~MEM x [cv;rv;g1;z1;g2;z2;ev]` by
    (gen_tac >> disch_tac >>
     map_every (fn v => qpat_assum v mp_tac)
       [`cv = _`,`rv = _`,`g1 = _`,`z1 = _`,`g2 = _`,`z2 = _`,`ev = _`] >>
     qpat_x_assum `not_fresh_at s2 x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >>
     metis_tac[arithmeticTheory.LE_ADD]) >>
  `(!x. not_fresh_at s2 x ==>
      lookup_var x ec = lookup_var x t' /\
      FLOOKUP Gc x = FLOOKUP G' x /\
      op_taint tc (Var x) = op_taint tn' (Var x)) /\
    tc.t_mem = tn'.t_mem /\ tc.t_stor = tn'.t_stor /\
    tc.t_trans = tn'.t_trans /\ tc.t_imm = tn'.t_imm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (ec = _)`,`Abbrev (u7 = _)`,`Abbrev (u6 = _)`,
        `Abbrev (u5 = _)`,`Abbrev (u4 = _)`,`Abbrev (u3 = _)`,
        `Abbrev (u2 = _)`,`Abbrev (u1 = _)`,`Abbrev (e0 = _)`,
        `Abbrev (Gc = _)`,`Abbrev (tc = _)`,`Abbrev (ws = _)`,
        `~bad1`,`~bad2`,
        `!x. not_fresh_at s2 x ==> ~MEM x _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
     `~MEM x [cv;rv;g1;z1;g2;z2;ev]` by (simp[MEM] >> metis_tac[]) >>
     fs[MEM,jump_to_def,update_var_def,lookup_var_def,
        finite_mapTheory.FLOOKUP_DRESTRICT,op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_LIST_THM]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx ee G' tn' t'` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
       stmt_state_rel _ _ _ _ _ _ _ /\ _` drule >> strip_tac >>
     drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     disch_then irule >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (qexists_tac `s2` >> simp[] >>
        conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx ee Gc tc ec` by
    (gen_tac >> disch_tac >>
     irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ G' tn' t'` drule >>
     disch_then (irule_at Any) >> qexists_tac `s2` >> simp[] >>
     conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     simp[Abbr `ec`,Abbr `u7`,Abbr `u6`,Abbr `u5`,Abbr `u4`,
       Abbr `u3`,Abbr `u2`,Abbr `u1`,Abbr `e0`,jump_to_def,update_var_def]) >>
  `!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
     not_local_ptr cenv ee.scopes x` by
    (rpt strip_tac >> irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `s2` >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee ec` by
    (gen_tac >> disch_tac >>
     `stmt_state_rel H ctx func cenv cx ee t'` by metis_tac[] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`stmt_state_rel H ctx func cenv cx ee t'`,
        `!x. MEM x _ ==> not_local_ptr cenv ee.scopes x`,
        `Abbrev (ec = _)`,`Abbrev (u7 = _)`,`Abbrev (u6 = _)`,
        `Abbrev (u5 = _)`,`Abbrev (u4 = _)`,`Abbrev (u3 = _)`,
        `Abbrev (u2 = _)`,`Abbrev (u1 = _)`,`Abbrev (e0 = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
     simp[stmt_state_rel_jump_to] >>
     rpt (irule stmt_state_rel_update_var >>
       conj_tac >- metis_tac[]) >>
     simp[stmt_state_rel_jump_to]) >>
  `ec.vs_allocas = t'.vs_allocas /\
   ec.vs_alloca_next = t'.vs_alloca_next /\ ec.vs_inst_idx = 0` by
    simp[Abbr `ec`,Abbr `u7`,Abbr `u6`,Abbr `u5`,Abbr `u4`,
      Abbr `u3`,Abbr `u2`,Abbr `u1`,Abbr `e0`,jump_to_def,update_var_def] >>
  `alloca_history func ec` by
    metis_tac[allocaHistoryTheory.alloca_history_jump] >>
  `return_buf_frame d cenv s2 ec` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`t2`,`s2`] >> simp[]) >>
  `~MEM q [cv;rv;g1;z1;g2;z2;ev]` by
    (simp[MEM] >> fs[ASCIInumbersTheory.toString_inj]) >>
  `lookup_var q ec = lookup_var q t' /\
   FLOOKUP Gc q = FLOOKUP G' q /\
   op_taint tc (Var q) = op_taint tn' (Var q)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (ec = _)`,`Abbrev (u7 = _)`,`Abbrev (u6 = _)`,
        `Abbrev (u5 = _)`,`Abbrev (u4 = _)`,`Abbrev (u3 = _)`,
        `Abbrev (u2 = _)`,`Abbrev (u1 = _)`,`Abbrev (e0 = _)`,
        `Abbrev (Gc = _)`,`Abbrev (tc = _)`,`Abbrev (ws = _)`,
        `~bad1`,`~bad2`,`~MEM q _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
     fs[MEM,jump_to_def,update_var_def,lookup_var_def,
        finite_mapTheory.FLOOKUP_DRESTRICT,op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_LIST_THM]) >>
  `ptr_covers Gc tc q ec 32` by
    fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `!name b len. local_region cenv ee.scopes ec name b len ==>
    regions_disjoint (w2n w) 32 b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes t' name b len` by
       (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.local_region_kept) >>
        conj_tac >-
          (qexistsl_tac [`ee`,`ec`,`s2`] >> simp[] >> metis_tac[]) >>
        qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`func`] >>
        first_x_assum irule >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  `FLOOKUP Gc cv = NONE /\ FLOOKUP Gc ev = NONE /\
   op_taint tc (Var cv) = {} /\ op_taint tc (Var ev) = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (Gc = _)`,`Abbrev (tc = _)`,`Abbrev (ws = _)`,
        `~bad1`,`~bad2`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
     simp[finite_mapTheory.FLOOKUP_DRESTRICT,op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_LIST_THM]) >>
  `lookup_var ev ec = SOME (i2w n2) /\
   lookup_var cv ec = SOME (i2w n1)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (ec = _)`,`Abbrev (u7 = _)`,`Abbrev (u6 = _)`,
        `Abbrev (u5 = _)`,`Abbrev (u4 = _)`,`Abbrev (u3 = _)`,
        `Abbrev (u2 = _)`,`Abbrev (u1 = _)`,`Abbrev (e0 = _)`,
        `ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev]`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
     fs[ALL_DISTINCT,MEM,jump_to_def,update_var_def,lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
     wordsLib.WORD_DECIDE_TAC) >>
  `~ec.vs_halted /\ ec.vs_current_bb = cond_lbl /\ allocas_from lo ec` by
    (fs[Abbr `ec`,Abbr `u7`,Abbr `u6`,Abbr `u5`,Abbr `u4`,
      Abbr `u3`,Abbr `u2`,Abbr `u1`,Abbr `e0`,jump_to_def,update_var_def,
      allocas_from_def] >>
     metis_tac[Abbr `ec`, Abbr `u7`, Abbr `u6`, Abbr `u5`, Abbr `u4`,
       Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `e0`, jump_to_def,
       update_var_def, allocas_from_def]) >>
  simp[get_range_limits_def,lift_sum_def,bind_def,return_def,
    check_def,assert_def,compatible_bound_def,GSYM listTheory.MAP_GENLIST] >>
  simp_tac (srw_ss()) [bind_return,ignore_bind_def] >>
  `assert T (Error (RuntimeError "For too long")) = return ()` by
    simp[FUN_EQ_THM,vyperStateTheory.assert_def,vyperStateTheory.return_def] >>
  simp[bind_return] >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  (conj_tac >- simp[evaluate_storage_trace_frame]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gc`,`ec`,`tc`] >>
  (conj_tac >-
    (gen_tac >> disch_tac >>
     irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G'`,`e0`,`tn'`] >>
     (reverse conj_tac >- (simp[Abbr `ec`] >> metis_tac[])) >>
     irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G'`,`t'`,`tn'`] >> simp[])) >>
  once_rewrite_tac[GSYM listTheory.MAP_GENLIST] >>
  `GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)) <> [] ==>
    body_stmts_full_ok cx stmts` by
    (strip_tac >>
     `body_for_full_ok cx tyv id stmts
       (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))` by
       (qpat_assum `!s3 vs t3 s4 t4. _` irule >>
        conj_tac >-
          (qexistsl_tac [`es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
             gas_explicit marks2 t.vs_gas_readings`,`ee`] >>
           qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
             (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
           pure_once_rewrite_tac [bind_def] >>
           asm_simp_tac (srw_ss()) [] >>
           pure_once_rewrite_tac [bind_def] >>
           asm_simp_tac (srw_ss()) [APPEND_NIL] >>
           simp[bind_def,return_def,lift_sum_def,get_range_limits_def,
             listTheory.MAP_GENLIST, combinTheory.o_DEF] >>
           simp[vyperStateTheory.evaluation_state_component_equality]) >>
        qexistsl_tac [`ee`,`ee`] >>
        simp[check_def,assert_def,compatible_bound_def,return_def]) >>
     fs[body_for_full_ok_def] >> first_x_assum irule >>
     qexistsl_tac [`ee`,`IntV n1`,`ee`] >>
     qpat_x_assum `GENLIST _ (Num (n2-n1)) <> []` mp_tac >>
     Cases_on `Num (n2-n1)` >> simp[GENLIST_CONS,read_result_def,return_def]) >>
  mp_tac (Q.INST [`tops` |-> `cx_tops cx`,
    `it` |-> `Range e1 e2`, `typ` |-> `expr_type e1`,
    `sa` |-> `s2`, `s0` |-> `t2`, `G0` |-> `G2`, `tn0` |-> `tn2`,
    `es` |-> `ee`, `Gentry` |-> `Gc`, `tnentry` |-> `tc`,
    `bc` |-> `pbc`, `bc_out` |-> `pbc_out`,
    `sb0` |-> `body_in`, `sb1` |-> `body_out`, `sj` |-> `pj`,
    `shadow_body_in` |-> `shadow_body_in`, `shadow_body_out` |-> `shadow_body_out`,
    `cv` |-> `STRING #"%" (toString (s2.cs_next_var + 1))`,
    `ev` |-> `STRING #"%" (toString (s2.cs_next_var + 7))`,
    `nv` |-> `STRING #"%" (toString pj.cs_next_var)`,
    `j1` |-> `s2.cs_next_id + 12`, `j2` |-> `s2.cs_next_id + 13`,
    `jstore` |-> `s2.cs_next_id + 14`] (SPEC_ALL for_range_continue_full)) >>
  (impl_tac >-
    (asm_rewrite_tac [] >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >-
       (qpat_assum `ce_locals_declared cenv env` mp_tac >>
        qpat_assum `id NOTIN FDOM env.var_types` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `FLOOKUP cenv.ce_vars id` >>
        simp[ce_locals_declared_def] >> metis_tac[])) >>
     (conj_tac >-
       (irule stmtSimPropsTheory.ret_pc_ok_frame >>
        qexistsl_tac [`cenv`,`t`,`s1`] >> simp[] >>
        (conj_tac >-
          (qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[expr_post_def] >> metis_tac[])) >>
        irule stmtSimPropsTheory.ret_pc_ok_frame >>
        qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
        qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[expr_post_def] >> metis_tac[])) >>
     (conj_tac >-
       (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `s1` >> simp[] >>
        metis_tac[cs_extends_def])) >>
     (conj_tac >-
       simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
     (conj_tac >-
       simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj]) >>
     (conj_tac >-
       (rpt gen_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def,
         ASCIInumbersTheory.toString_inj] >> metis_tac[])) >>
     simp[ASCIInumbersTheory.toString_inj] >>
     (conj_tac >-
       (irule lookup_block_fn_insts >>
        qpat_assum `lookup_block s2.cs_current_bb _ = _` (irule_at Any) >> simp[])) >>
     (conj_tac >-
       (`body_in.cs_next_var <= body_out.cs_next_var` by
          (qpat_assum `compile_stmts _ _ _ stmts body_in = _` mp_tac >>
           mp_tac (cj 2 compile_stmt_cs_mono) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp[cs_mono_def] >> metis_tac[]) >>
        qpat_assum `suffix _ _ _ _ body_out = _` mp_tac >>
        qpat_assum `emit_jmp_if_not_terminated _ body_out = _` mp_tac >>
        qpat_assum `Abbrev (suffix = _)` mp_tac >>
        qpat_assum `body_in.cs_next_var = _` mp_tac >>
        qpat_assum `pj.cs_next_var = _` mp_tac >>
        qpat_assum `body_in.cs_next_var <= body_out.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        qpat_x_assum `suffix _ _ _ _ body_out = _` mp_tac >>
        simp[Abbr `suffix`,comp_bind_def,comp_ignore_bind_def] >>
        simp[new_block_def,emit_op_def,emit_inst_def,fresh_var_def,fresh_id_def,
          emit_def,comp_bind_def,comp_return_def,comp_ignore_bind_def,LET_THM] >>
        strip_tac >> gvs[])) >>
     (conj_tac >-
       (qpat_assum `r.cs_current_insts = []` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[block_is_terminated_def])) >>
     (conj_tac >-
       (qpat_assum `gas_admissible (eval_stmt _ _) _ es` mp_tac >>
        qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _` mp_tac >>
        qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _` mp_tac >>
        qpat_assum `evaluate_type _ (expr_type e1) = SOME tyv` mp_tac >>
        qpat_assum `n1 <= n2` mp_tac >>
        qpat_assum `Num (n2-n1) <= n` mp_tac >>
        qpat_assum `ee.gas_obs = []` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        qpat_x_assum `gas_admissible _ _ _` mp_tac >>
        simp[Once evaluate_def,lift_option_type_def] >>
        simp[Once evaluate_def,bind_assoc] >>
        simp[bind_return] >>
        once_rewrite_tac[GSYM bind_assoc] >> strip_tac >>
        drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
        simp[bind_return] >>
        once_rewrite_tac[GSYM bind_assoc] >> strip_tac >>
        drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
        simp[bind_return,lift_sum_def,get_range_limits_def,
          check_def,compatible_bound_def] >>
        simp[gasContextTheory.gas_admissible_def,ignore_bind_def,
          vyperStateTheory.bind_def,vyperStateTheory.assert_def])) >>
     qpat_x_assum `cv = _` SUBST_ALL_TAC >>
     qpat_x_assum `ev = _` SUBST_ALL_TAC >> simp[])) >>
  disch_tac >>
  fs[listTheory.MAP_GENLIST,combinTheory.o_DEF] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  first_assum (irule_at Any) >>
  reverse conj_tac >-
    (rpt gen_tac >> disch_then mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> qexists_tac `cenv` >> simp[] >>
  qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `ghost_kept_at _ _ _ sa _ _ _ _ _` mp_tac >>
  qpat_assum `ghost_kept_at _ _ _ s1 _ _ _ _ _` mp_tac >>
  qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
  qpat_assum `s1.cs_next_var <= s2.cs_next_var` mp_tac >>
  qpat_assum `!x v. not_fresh_at s2 x /\ _ ==> _` mp_tac >>
  qpat_assum `!aid bl. FLOOKUP t2.vs_allocas aid = SOME bl ==> _` mp_tac >>
  qpat_assum `!x. not_fresh_at s2 x ==> FLOOKUP G'' x = _ /\ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[expr_post_def,ghost_kept_at_def] >> rpt strip_tac >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Finalise body_for_range_checked_full

Theorem body_for_range_full:
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (?e1 e2. it = Range e1 e2) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `?a1 n1 a2 n2.
    it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))`
  >- (irule body_for_range_lit_full >> metis_tac[]) >>
  irule body_for_range_checked_full >> metis_tac[]
QED
