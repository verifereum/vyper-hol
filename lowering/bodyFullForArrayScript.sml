(* Array control boundaries on one concrete run.  Sequence-pointer
   certificates are internal assembly obligations, with fixed ghosts before H. *)
Theory bodyFullForArray
Ancestors
  bodyFullForRange fragGasOriginPtrLoop fragGasSeqPtr fragGasSeqMem
  fragExecMem instMemFrontier venomExecSemantics venomExecProofs venomInst
  venomState ptrDiscipline list rich_list words fragExec exprLoweringProps
  memSafeRun bodyPtrPrecompileBuiltinsSuffix finite_map
  stmtSimForArrayLoop stmtForArrayMemoryCopy bodyDeclMemoryCounted
  stmtLowering emitHelper compileEnv

Theorem for_array_assign_jump_path_full:
  code = [mk_inst i ASSIGN [Lit 0w] [idx]] /\
  bb = <|bb_label := lbl; bb_instructions :=
    code ++ [mk_inst j JMP [Label cond] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code s Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to cond (update_var idx 0w s)),G',tn')
Proof
  strip_tac >>
  qabbrev_tac `u = update_var idx 0w s` >>
  `run_inst_seq code s = OK u` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,Abbr `u`] >>
  `run_inst_seq_mem_ok code s` by
    simp[run_inst_seq_mem_ok_def,mk_inst_def,below_frontier_no_ranges,
         inst_dload_in_section_other,step_inst_base_opcode_eqs,
         eval_operand_def] >>
  qexistsl_tac [`Gf`,`tf`] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := 1),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 1,Gf,tf) []
     (OK (jump_to cond (u with vs_inst_idx := 1)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,get_instruction_def,allocas_from_def] >>
     qexists_tac `j` >> simp[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`]
QED

Theorem for_array_cond_path_full:
  code = [mk_inst j1 EQ [Var idx; bound_op] [dv]] /\
  bb = <|bb_label := lbl; bb_instructions := code ++
       [mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  lookup_var idx cc = SOME a /\ eval_operand bound_op cc = SOME b /\
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
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,Abbr `u`] >>
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
  drule_all gas_origin_ptr_path_trans >>
  simp[jump_to_def,Abbr `u`,bool_to_word_def]
QED

Theorem for_array_incr_path_full:
  code = [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
          mk_inst i2 ASSIGN [Var nv] [idx]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
  lookup_var idx dd = SOME c /\
  ~ctx_has_dalloca ctx /\ allocas_from lo dd /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code dd Gf tf) ==>
  ?G' tn'. !H.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
      (OK (jump_to cond_lbl
        (update_var idx (c+1w) (update_var nv (c+1w) dd))),G',tn')
Proof
  strip_tac >> irule for_range_incr_path_full >> metis_tac[]
QED

Theorem for_array_memory_element_path_full:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  not_fresh_at sa p /\
  w2n arr_base + k * stride + stride <= s.vs_alloca_next /\
  w2n dst + stride <= s.vs_alloca_next /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  code = ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
           mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0) /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code s Gf tf) ==>
  ?t. run_inst_seq code s = OK t /\
    stmt_state_rel H0 ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb0) /\
    (!b len. b + len <= w2n dst \/ w2n dst + stride <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!caller. caller.cs_next_id <= sa.cs_next_id /\
      caller.cs_next_id <= ainst.inst_id ==>
      alloca_frame cenv es caller s bc
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
            :: es.scopes) t) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tf))
Proof
  strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`,`j4`] strip_assume_tac) >>
  `run_inst_seq_mem_ok code s` by
    (`!x. x = ep \/ x = p ==> not_fresh_at sa x` by metis_tac[] >>
     drule_all array_body_prefix_mem_ok >>
     disch_then (qspecl_then [`j4`,`j3`] mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (Cases_on `is_word_type et`
     >- (gvs[compile_iter_elem_copy_def,emit_op_def,emit_void_def,
             comp_bind_def,comp_ignore_bind_def,comp_return_def,
             fresh_id_def,fresh_var_def,emit_def,LET_THM] >>
         gvs[emitted_insts_def,mk_inst_def] >>
         rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]) >>
     irule compile_store_memory_same_no_gas >>
     gvs[compile_iter_elem_copy_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[mk_inst_def,is_terminator_def] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[mk_inst_def] >> gvs[FILTER_EQ_NIL,EVERY_MEM]) >>
  `run_inst_seq code s = OK t` by metis_tac[] >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[] >>
  simp[] >> conj_tac >- gvs[] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED
