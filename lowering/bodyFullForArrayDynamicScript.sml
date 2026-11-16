Theory bodyFullForArrayDynamic
Ancestors
  bodyFullForArray whitelistForIterDynLoop stmtSimForArray
  stmtForArrayMemoryCopy fragExecMem memSafeRun instMemFrontier
  venomExecSemantics venomExecProofs venomState venomInst stmtLowering emitHelper
  exprLoweringProps emitHelperProps compileEnv words arithmetic list rich_list
  bodyDeclMemoryCounted fragGasOriginPtrLoop fragGasSeqPtr

Theorem for_array_dynamic_element_path_full:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  not_fresh_at sa p /\
  w2n arr_base + 32 + k * stride + stride <= s.vs_alloca_next /\
  w2n dst + stride <= s.vs_alloca_next /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  code = ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
           mk_inst j4 ADD [Lit 32w; Var ov] [tot];
           mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0) /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code s Gf tf) ==>
  ?t. run_inst_seq code s = OK t /\
    stmt_state_rel H0 ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
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
  drule_all dynarray_for_body_entry_run >>
  disch_then (qspecl_then [`j3`,`j4`,`j5`] strip_assume_tac) >>
  `run_inst_seq_mem_ok code s` by
    (qpat_assum `code = _` (fn th => pure_rewrite_tac[th]) >>
     irule run_inst_seq_mem_ok_append >>
     reverse conj_tac
     >- (irule run_inst_seq_mem_ok_every >>
         simp[mk_inst_def, inst_dload_in_section_def] >>
         rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]) >>
     drule_all dynarray_address_prefix_run >> simp[] >> rpt strip_tac >> gvs[] >>
     irule array_iter_copy_mem_ok >>
     goal_assum (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     qexistsl_tac [`dst`, `n2w (w2n arr_base + 32 + k * type_memory_size tv)`, `v`] >>
     simp[eval_operand_def, lookup_var_update_var, update_var_def, w2n_n2w] >>
     metis_tac[]) >>
  `!b len. b + len <= w2n dst \/ w2n dst + stride <= b ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (qabbrev_tac `u = update_var ep (n2w (w2n arr_base + 32 + k * stride))
       (update_var tot (n2w (32 + k * stride))
         (update_var ov (n2w (k * stride)) s))` >>
     `eval_operand (Var ep) u = SOME (n2w (w2n arr_base + 32 + k * stride)) /\
      eval_operand (Var p) u = SOME dst` by
       simp[Abbr `u`,eval_operand_def,lookup_var_update_var] >>
     `val_in_memory tv v
        (w2n (n2w (w2n arr_base + 32 + k * stride) : bytes32)) u.vs_memory` by
       gvs[Abbr `u`,update_var_def,w2n_n2w] >>
     `!x. Var ep = Var x ==> not_fresh_at sa x` by simp[] >>
     `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
     `type_memory_bytes cenv et = type_memory_size tv /\
      type_memory_size tv + 64 < dimword (:256)` by metis_tac[] >>
     drule_all array_iter_copy_run >> strip_tac >>
     drule_all dynarray_address_prefix_run >>
     disch_then (qspecl_then [`stride`,`ep`,`j3`,`j4`,`j5`]
       (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append)) >>
     gvs[Abbr `u`,update_var_def] >> metis_tac[]) >>
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
