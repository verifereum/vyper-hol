(* Concrete scalar control packets, with one endpoint and ghost before H. *)
Theory bodyFullForArrayLocalControl
Ancestors forPtrAdmin forPtrCheckedScalar instSeqPtrLo
  fragGasSeqPtr fragGasOriginPtrLoop fragGasSeqMem instMemFrontier
  fragExecMem memSafeRun exprLoweringProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  finite_map pred_set words list rich_list codegenRel contextCodegenRel

Theorem for_array_local_condition_full:
  code = [mk_inst j1 EQ [Var idx; bound_op] [dv]] /\
  bb = <|bb_label := lbl; bb_instructions := code ++
       [mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  lookup_var idx cc = SOME a /\ eval_operand bound_op cc = SOME b /\
  ~ctx_has_dalloca ctx /\ allocas_from lo cc /\ lo <= cc.vs_alloca_next /\
  FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
  op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} ==>
  ?sf Gf tf.
    sf = jump_to (if a=b then exit_lbl else body_lbl)
           (update_var dv (bool_to_word (a=b)) cc) /\
    Gf = DRESTRICT G (COMPL {dv}) /\
    tf = (tn with t_var := tn.t_var |+ (dv,{})) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (cc,G,tn) []
           (OK sf,Gf,tf)) /\
    sf.vs_current_bb = (if a=b then exit_lbl else body_lbl) /\
    sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    lookup_var dv sf = SOME (bool_to_word (a=b)) /\
    FLOOKUP Gf dv = NONE /\ op_taint tf (Var dv) = {} /\
    sf.vs_memory = cc.vs_memory /\ sf.vs_allocas = cc.vs_allocas /\
    sf.vs_alloca_next = cc.vs_alloca_next /\ sf.vs_fmp = cc.vs_fmp /\
    sf.vs_requests = cc.vs_requests /\ sf.vs_call_ctx = cc.vs_call_ctx /\
    sf.vs_accounts = cc.vs_accounts /\ sf.vs_transient = cc.vs_transient /\
    sf.vs_immutables = cc.vs_immutables /\ sf.vs_labels = cc.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x <> dv ==> lookup_var x sf = lookup_var x cc /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var dv (bool_to_word (a=b)) cc` >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code cc
       (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))`
    by suspend "certificate" >>
  qexistsl_tac [`jump_to (if a=b then exit_lbl else body_lbl) u`,
    `DRESTRICT G (COMPL {dv})`, `tn with t_var := tn.t_var |+ (dv,{})`] >>
  simp[Abbr `u`] >> conj_tac
  >- suspend "path" >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def]
QED

Resume for_array_local_condition_full[certificate]:
  gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
  qexists_tac `D` >> simp[inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_eq >> simp[op_prov_def]) >>
  simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,eval_operand_def] >>
  `new_site_bytes cc u = {}` by
    simp[Abbr `u`,new_site_bytes_def,update_var_def,FLOOKUP_DEF,
         EXTENSION,SF CONJ_ss] >>
  simp[step_prov_def,set_prov_def,out_prov_def,step_taint_def,
       set_var_taint_def,out_taint_def,mem_taint_def,step_writes_def,
       source_memory_write_ranges_def,written_taint_def,store_taint_def,
       adopt_reset_def,imm_taint_def,range_bytes_def,mk_inst_def,
       Abbr `u`,taint_component_equality] >>
  gvs[eval_operand_def]
QED

Resume for_array_local_condition_full[path]:
  qabbrev_tac `u = update_var dv (bool_to_word (a=b)) cc` >>
  `run_inst_seq code cc = OK u` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,Abbr `u`] >>
  `run_inst_seq_mem_ok code cc` by
    (irule run_inst_seq_mem_ok_every >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  gen_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (cc,G,tn) []
     (OK (u with vs_inst_idx := 1),DRESTRICT G (COMPL {dv}),
       tn with t_var := tn.t_var |+ (dv,{}))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 1,DRESTRICT G (COMPL {dv}),
       tn with t_var := tn.t_var |+ (dv,{})) []
     (OK (jump_to (if bool_to_word (a=b) <> 0w then exit_lbl else body_lbl)
          (u with vs_inst_idx := 1)),DRESTRICT G (COMPL {dv}),
       tn with t_var := tn.t_var |+ (dv,{}))` by
    (irule jnz_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,eval_operand_def,
          lookup_var_def,FLOOKUP_UPDATE,allocas_from_def,op_taint_def] >>
     reverse conj_tac >- gvs[allocas_from_def] >>
     qexistsl_tac [`Var dv`,`j2`] >>
     gvs[get_instruction_def,update_var_def,eval_operand_def,
         lookup_var_def,FLOOKUP_UPDATE]) >>
  drule_all gas_origin_ptr_path_trans >>
  simp[jump_to_def,Abbr `u`,bool_to_word_def]
QED

Finalise for_array_local_condition_full

Theorem scalar_seq_intro[local]:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) code
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) Gf tf ==>
  inst_seq_ptr D 0 ctx fn PG G tn (mk_inst id opc ops [out] :: code) s Gf tf
Proof
  metis_tac[for_checked_scalar_seq_cons]
QED

Theorem for_array_local_increment_full:
  code = [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
          mk_inst i2 ASSIGN [Var nv] [idx]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
  lookup_var idx dd = SOME c /\
  ~ctx_has_dalloca ctx /\ allocas_from lo dd /\ lo <= dd.vs_alloca_next /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\ idx <> nv ==>
  ?sf Gf tf.
    sf = jump_to cond_lbl (update_var idx (c+1w) (update_var nv (c+1w) dd)) /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}) /\
    tf = (tn with t_var := tn.t_var |+ (nv,{}) |+ (idx,{})) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
           (OK sf,Gf,tf)) /\
    sf.vs_current_bb = cond_lbl /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    lookup_var idx sf = SOME (c+1w) /\ lookup_var nv sf = SOME (c+1w) /\
    FLOOKUP Gf idx = NONE /\ FLOOKUP Gf nv = NONE /\
    op_taint tf (Var idx) = {} /\ op_taint tf (Var nv) = {} /\
    sf.vs_memory = dd.vs_memory /\ sf.vs_allocas = dd.vs_allocas /\
    sf.vs_alloca_next = dd.vs_alloca_next /\ sf.vs_fmp = dd.vs_fmp /\
    sf.vs_requests = dd.vs_requests /\ sf.vs_call_ctx = dd.vs_call_ctx /\
    sf.vs_accounts = dd.vs_accounts /\ sf.vs_transient = dd.vs_transient /\
    sf.vs_immutables = dd.vs_immutables /\ sf.vs_labels = dd.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x sf = lookup_var x dd /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code dd
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}))
    (tn with t_var := tn.t_var |+ (nv,{}) |+ (idx,{}))`
    by suspend "certificate" >>
  qexistsl_tac [`jump_to cond_lbl (update_var idx (c+1w) (update_var nv (c+1w) dd))`,
    `DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx})`,
    `tn with t_var := tn.t_var |+ (nv,{}) |+ (idx,{})`] >>
  simp[] >> conj_tac >- suspend "path" >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,op_taint_def]
QED

Resume for_array_local_increment_full[certificate]:
  gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
  qexists_tac `D` >>
  gvs[] >> irule scalar_seq_intro >> gvs[op_taint_def,op_prov_def] >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  qexists_tac `c+1w` >>
  simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def,exec_pure2_def] >>
  rewrite_tac[GSYM mk_inst_def] >> irule scalar_seq_intro >>
  simp[op_taint_def,op_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] >>
  qexists_tac `c+1w` >>
  simp[op_taint_def,op_prov_def,step_inst_base_opcode_eqs,mk_inst_def,
       eval_operand_def,exec_pure2_def,update_var_def,lookup_var_def,
       FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,inst_seq_ptr_def]
QED

Resume for_array_local_increment_full[path]:
  qabbrev_tac `u = update_var idx (c+1w) (update_var nv (c+1w) dd)` >>
  `run_inst_seq code dd = OK u` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,Abbr `u`,lookup_var_def,
         update_var_def,FLOOKUP_UPDATE] >>
  `run_inst_seq_mem_ok code dd` by
    (irule run_inst_seq_mem_ok_every >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  gen_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
     (OK (u with vs_inst_idx := 2),
      DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}),
      tn with t_var := tn.t_var |+ (nv,{}) |+ (idx,{}))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 2,
      DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}),
      tn with t_var := tn.t_var |+ (nv,{}) |+ (idx,{})) []
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)),
      DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}),
      tn with t_var := tn.t_var |+ (nv,{}) |+ (idx,{}))` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,allocas_from_def] >>
     reverse conj_tac >- gvs[allocas_from_def] >>
     qexists_tac `i3` >> gvs[get_instruction_def]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`]
QED

Finalise for_array_local_increment_full
