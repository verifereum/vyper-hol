Theory bodyConcatBytesCopyMods
Ancestors
  bodyConcatCutsMods bodyFullBuiltinConcatHead bodyPtrBytestringBuiltinsConcatOperand
  bodyFullHashKeccakFixed exprSimWordArgs stateRelProj exprOperandVar
  exprSimProps venomExecSemantics eventTopicValueProps
  exprSimMemDefs compileEnv vyperValue vyperTyping vyperAST venomState words
  bodyFullPostsMods exprLoweringProps exprSimFullBundleProps loweringPosts valueEncodingDefs
Libs monadsyntax

Theorem concat_bytes_store_frontier[local]:
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  expr_store_bound cx (post_value_type cenv e) v op s /\
  eval_operand op s = SOME w ==>
  w2n w + 32 + LENGTH (concat_payload_mods v) <= s.vs_alloca_next
Proof
  rpt strip_tac >>
  `~is_word_type (expr_type e)` by simp[bytestring_type_not_word] >>
  `val_store_size tv v = 0 \/ w2n w + val_store_size tv v <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def] >> metis_tac[]) >>
  `(?n. expr_type e = BaseT (BytesT (Dynamic n))) \/
   (?n. expr_type e = BaseT (StringT n))` by
    (Cases_on `expr_type e` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_bytestring_type_def]) >>
  gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def,val_store_size_def,concat_payload_mods_def] >>
  qmatch_asmsub_abbrev_tac `word_size len` >>
  qspec_then `len` mp_tac le_word_size_mul >> decide_tac
QED

Theorem concat_copy_memory_fields[local]:
  (mstore off w s).vs_immutables = s.vs_immutables /\
  (mstore off w s).vs_data_section = s.vs_data_section /\
  (mcopy dst src n s).vs_immutables = s.vs_immutables /\
  (mcopy dst src n s).vs_data_section = s.vs_data_section
Proof
  simp[mstore_def,mcopy_def,write_memory_with_expansion_def,LET_THM]
QED

Theorem concat_bytes_copy_cut_mods:
  (do arg_len <- emit_op MLOAD [op];
      arg_data <- emit_op ADD [op;Lit 32w];
      offset_op <- emit_op MLOAD [Var ov];
      dst <- emit_op ADD [Var dv;offset_op];
      emit_void MCOPY [dst;arg_data;arg_len];
      new_offset <- emit_op ADD [offset_op;arg_len];
      emit_void MSTORE [Var ov;new_offset]
   od) sc = ((),s2) /\
  fn_has_code sc s2 func /\ fn_inst_ids_distinct func /\
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (ee,sc,s,G,tn) bs /\
  concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e (es,sa,s0,G0,tn0)
    (op,sc) H (INL v) ee G tn s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  32 + LENGTH bs + concat_payload_capacity (expr_type e) <= bsz /\
  (!z. op = Var z ==> not_fresh_at sc z) /\
  local_ptrs_reserved cenv sc /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) ==>
  ?u G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')) /\
    concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
      (ee,sc,s,G,tn) (s2,u,G',tn') bs (concat_payload_mods v)
Proof
  simp[concat_live_mods_def,concat_head_post_mods_def,expr_post_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_post_state >> strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> drule stmt_state_rel_alloca_room >> metis_tac[]) >>
  drule_all concat_operand_bytes_read >>
  rewrite_tac[GSYM concat_payload_mods_def] >>
  disch_then (qx_choose_then `sw` (qx_choose_then `sp` strip_assume_tac)) >>
  qpat_x_assum `op = Var sp` SUBST_ALL_TAC >>
  `w2n sw + 32 + LENGTH (concat_payload_mods v) <= s.vs_alloca_next` by
    (irule concat_bytes_store_frontier >>
     qexistsl_tac [`cenv`,`cx`,`e`,`Var sp`,`tv`] >> simp[eval_operand_def]) >>
  `w2n sw + 32 + LENGTH (concat_payload_mods v) < dimword (:256) /\
   32 + LENGTH bs + LENGTH (concat_payload_mods v) <= bsz` by decide_tac >>
  `mload (w2n sw) s = n2w (LENGTH (concat_payload_mods v))` by
    fs[mload_def,mem_word_at_def] >>
  `lookup_var sp s = SOME (n2w (w2n sw)) /\
   lookup_var ov s = SOME (n2w (w2n ow)) /\ not_fresh_at sc sp` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] concat_head_bytes_uniform) >>
  disch_then (qspecl_then [`explicit`,`d`,`cx`,`PG`] strip_assume_tac) >>
  `u.vs_inst_idx = LENGTH s2.cs_current_insts /\
   u.vs_immutables = s.vs_immutables /\ u.vs_data_section = s.vs_data_section` by
    (qpat_assum `u = _` SUBST1_TAC >> simp[concat_copy_memory_fields]) >>
  `!z. not_fresh_at sc z ==> lookup_var z u = lookup_var z s` by
    (qpat_assum `u = _` (fn th => simp[th,lookup_var_def]) >> metis_tac[]) >>
  qpat_x_assum `u = _` kall_tac >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  simp[concat_copy_effect_mods_def,expr_sim_full_endpoint_def] >>
  qpat_x_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` mp_tac >>
  simp[]
QED
