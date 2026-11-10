Theory ctorDeployMemoryRunMemEntryFirstEmission
Ancestors
  compilerFirstEmission stmtLowering exprLowering compileEnv fragExec rich_list context
  builtinSimple builtinMath builtinMisc builtinHashing builtinBytes
  exprLoweringProps exprSimUnwrap builtinAbi builtinCreate
Libs
  monadsyntax

Theorem ctor_declare_local_code:
  declare_local ce id ty a = (ce',b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\
  a.cs_current_insts = b.cs_current_insts
Proof
  simp[declare_local_def] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_return_def, fresh_var_def] >>
  strip_tac >> gvs[] >> irule cs_extends_same_block >> simp[]
QED

Theorem ctor_declare_stmt_local_code:
  !ce stmt a ce' b. declare_stmt_local ce stmt a = (ce',b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\
  a.cs_current_insts = b.cs_current_insts
Proof
  gen_tac >> Cases >> simp[declare_stmt_local_def, comp_return_def,
    cs_extends_refl] >> metis_tac[ctor_declare_local_code]
QED

Theorem ctor_stmts_first_emission_lift:
  (!ce lc ty stmt a x b. compile_stmt ce lc ty stmt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !ss ce lc ty a x b. compile_stmts ce lc ty ss a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> Induct
  >- simp[compile_stmt_def, comp_return_def, cs_extends_refl] >>
  ntac 4 gen_tac >> simp_tac bool_ss [Once compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_get] >>
  gen_tac >> IF_CASES_TAC
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_declare_stmt_local_code] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >>
  metis_tac[]
QED

Theorem ctor_fresh_label_code:
  fresh_label s a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\
  a.cs_current_insts = b.cs_current_insts
Proof
  simp[fresh_label_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem ctor_ifexp_first_emission:
  !ce cb ct env ty ann cond yes no.
  (!a x b. lower_value ce env (BaseT BoolT) cond a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) /\
  cs_appends (ce env ty yes) /\ cs_appends (ce env ty no) /\
  (!v. cs_appends (compile_ifexp_arm env (expr_type (IfExp ann cond yes no))
                   (lowered_value_type env yes) v)) /\
  (!v. cs_appends (compile_ifexp_arm env (expr_type (IfExp ann cond yes no))
                   (lowered_value_type env no) v)) ==>
  !a x b. compile_expr_body ce cb ct env ty (IfExp ann cond yes no) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 9 gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_fresh] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_fresh_label_code] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_fresh_label_code] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_fresh_label_code] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `x` >>
      irule (cj 1 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  simp_tac bool_ss [ETA_THM] >>
  rpt (CONV_TAC (DEPTH_CONV ETA_CONV) >> ho_match_mp_tac cs_appends_bind >> conj_tac
       >- simp[cs_appends_prims, cs_appends_emit_helpers] >> gen_tac) >>
  simp[cs_appends_def, cs_extends_refl] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[cs_extends_refl]
QED


Theorem ctor_flag_member_first_emission:
  !ce cb ct env ty ann nsid member a x b.
  compile_expr_body ce cb ct env ty (FlagMember ann nsid member) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  simp[compile_expr_body_def, cs_extends_refl] >>
  rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_top_level_name_first_emission:
  !ce cb ct env ty ann nsid a x b.
  compile_expr_body ce cb ct env ty (TopLevelName ann nsid) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 7 gen_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  Cases_on `FLOOKUP env.ce_module_vars nsid`
  >- (simp_tac (srw_ss()) [] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt gen_tac >> Cases_on `x` >> strip_tac >>
          qspec_then `INVALID` mp_tac (cj 1 first_emission_emit_helpers) >>
          simp[] >> disch_then drule >> metis_tac[]) >>
      simp[cs_extends_refl] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  Cases_on `x` >> simp[cs_extends_refl] >>
  rpt gen_tac >>
  Cases_on `emit_inst INVALID [] [] a` >>
  rename1 `emit_inst INVALID [] [] a = (u,c)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  qspec_then `INVALID` mp_tac (cj 1 first_emission_emit_helpers) >>
  simp[] >> disch_then drule >> metis_tac[]
QED

Theorem ctor_alloc_buffer_first_emission:
  !size a x b. compile_alloc_buffer size a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (qspec_then `ALLOCA` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  simp[comp_return_def, cs_extends_refl] >> rpt strip_tac >>
  gvs[cs_extends_refl]
QED

Theorem ctor_imm_load_word_first_emission:
  !is_ctor imm off a x b.
    compile_imm_load_word is_ctor imm off a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> reverse (Cases_on `is_ctor`)
  >- (simp[compile_imm_load_word_def] >>
      qspec_then `DLOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  Cases_on `imm`
  >- (simp[compile_imm_load_word_def] >>
      qspec_then `ILOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  simp_tac (srw_ss()) [compile_imm_load_word_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (qspec_then `ADD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  qspec_then `ILOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_ptr_load_first_emission:
  !is_ctor imm loc op a x b.
    compile_ptr_load is_ctor imm loc op a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 4 gen_tac >> Cases_on `loc` >>
  rewrite_tac[compile_ptr_load_def]
  >- (qspec_then `MLOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[])
  >- (qspec_then `SLOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[])
  >- (qspec_then `TLOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[])
  >- metis_tac[ctor_imm_load_word_first_emission] >>
  qspec_then `CALLDATALOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_multi_vvs_first_emission:
  !cfn.
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !es env a x b. compile_multi_vvs cfn env es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> strip_tac >> Induct
  >- (simp[compile_multi_vvs_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl]) >>
  ntac 2 gen_tac >> rewrite_tac[compile_multi_vvs_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_ptr_load_appends:
  !is_ctor imm loc op. cs_appends (compile_ptr_load is_ctor imm loc op)
Proof
  simp[cs_appends_def] >> metis_tac[ctor_ptr_load_first_emission]
QED

Theorem ctor_ptr_store_appends:
  !is_ctor imm loc dst v. cs_appends (compile_ptr_store is_ctor imm loc dst v)
Proof
  ntac 5 gen_tac >> Cases_on `loc` >>
  simp[compile_ptr_store_def, compile_imm_store_word_def,
       cs_appends_emit_helpers] >>
  rpt gen_tac >> rpt IF_CASES_TAC >>
  simp[cs_appends_emit_helpers] >>
  Cases_on `imm` >> simp[cs_appends_emit_helpers] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_word_copy_loop_appends:
  !src dst n load_loc store_loc is_ctor.
    cs_appends (compile_word_copy_loop src dst n load_loc store_loc is_ctor)
Proof
  rpt gen_tac >>
  rewrite_tac[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
              compile_word_copy_loop_base_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- (simp[cs_appends_prims, cs_appends_emit_helpers,
                 ctor_ptr_load_appends, ctor_ptr_store_appends] >>
           ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
       rpt gen_tac) >>
  simp[cs_appends_prims, cs_appends_emit_helpers]
QED

Theorem ctor_lit_byte_offset_appends:
  !op off. cs_appends (compile_lit_byte_offset op off)
Proof
  rpt gen_tac >> simp[compile_lit_byte_offset_def] >>
  IF_CASES_TAC >> simp[cs_appends_return] >>
  Cases_on `op` >> simp[cs_appends_return, cs_appends_emit_helpers]
QED

Theorem ctor_imm_copy_to_memory_appends:
  !n is_ctor imm src dst off.
    cs_appends (compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, cs_appends_return] >>
  rpt gen_tac >> rewrite_tac[compile_imm_copy_to_memory_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- (simp[ctor_lit_byte_offset_appends, cs_appends_emit_helpers] >>
           rw[cs_appends_def] >> metis_tac[ctor_imm_load_word_first_emission]) >>
       rpt gen_tac) >>
  simp[]
QED

Theorem ctor_materialize_suffix_appends:
  (!src dst n. cs_appends (compile_storage_to_memory src dst n)) /\
  (!src dst n. cs_appends (compile_transient_to_memory src dst n))
Proof
  simp[compile_storage_to_memory_def, compile_transient_to_memory_def,
       ctor_word_copy_loop_appends]
QED

Theorem ctor_ensure_nonmemory_first_emission:
  !pop loc mem_bytes word_count is_ctor imm.
  loc <> LocMemory ==>
  !a x b. compile_ensure_in_memory pop loc mem_bytes word_count is_ctor imm a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 6 gen_tac >> Cases_on `loc` >> simp[] >>
  simp_tac (srw_ss()) [compile_ensure_in_memory_def, LET_THM] >>
  (ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- (qspec_then `CALLDATALOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
       simp[] >> metis_tac[ctor_alloc_buffer_first_emission]) >>
   gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
   Cases_on `word_count = 1` >> simp[] >>
   rpt (FIRST [ho_match_mp_tac cs_appends_bind,
               ho_match_mp_tac cs_appends_ignore_bind] >>
        rw[cs_appends_emit_helpers, ctor_materialize_suffix_appends,
           ctor_imm_copy_to_memory_appends, cs_appends_return]) >>
   rw[cs_appends_def] >> metis_tac[ctor_alloc_buffer_first_emission])
QED

Theorem ctor_ensure_in_memory_first_emission:
  !pop loc mem_bytes word_count is_ctor imm a x b.
  compile_ensure_in_memory pop loc mem_bytes word_count is_ctor imm a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 6 gen_tac >> Cases_on `loc = LocMemory`
  >- (gvs[compile_ensure_in_memory_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl]) >>
  metis_tac[ctor_ensure_nonmemory_first_emission]
QED

Theorem ctor_unwrap_value_first_emission:
  !env vv a x b. unwrap_value env vv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> Cases_on `vv`
  >- (simp[unwrap_value_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl]) >>
  simp_tac (srw_ss()) [unwrap_value_def, LET_THM] >>
  IF_CASES_TAC
  >- metis_tac[ctor_ptr_load_first_emission] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[comp_return_def] >> rpt strip_tac >>
  gvs[cs_extends_refl] >>
  metis_tac[ctor_ensure_in_memory_first_emission]
QED

Theorem ctor_store_byte_chunks_appends:
  !ptr bs off. cs_appends (compile_store_byte_chunks ptr bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp_tac (srw_ss()) [Once compile_store_byte_chunks_def, LET_THM] >>
  simp[cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >>
  simp[cs_appends_emit_helpers] >> gvs[]
QED

Theorem ctor_bytelike_literal_first_emission:
  !bs n a x b. compile_bytelike_literal bs n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> simp_tac (srw_ss()) [compile_bytelike_literal_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (ho_match_mp_tac cs_appends_ignore_bind >>
       rw[cs_appends_emit_helpers, ctor_store_byte_chunks_appends,
          cs_appends_return])
QED

(* A literal compiles either to a plain return or to one bytelike buffer
   allocation; splitting on the type here keeps the goals small. *)
Theorem ctor_literal_vv_shape[local]:
  !ty lit. (?v. compile_literal_vv ty lit = comp_return v) \/
    ?bs n. compile_literal_vv ty lit =
      do buf <- compile_bytelike_literal bs n;
         comp_return (LocatedValue ty (base_ptr buf)) od
Proof
  ntac 2 gen_tac >> Cases_on `lit` >> TRY (rename1 `BoolL flag` >> Cases_on `flag`) >>
  simp_tac (srw_ss()) [compile_literal_vv_def] >>
  BasicProvers.every_case_tac >> metis_tac[]
QED

Theorem ctor_literal_vv_first_emission:
  !ty lit a x b. compile_literal_vv ty lit a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >>
  strip_assume_tac (Q.SPECL [`ty`, `lit`] ctor_literal_vv_shape) >>
  pop_assum SUBST1_TAC
  >- (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_bytelike_literal_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[cs_appends_return]
QED

Theorem ctor_name_vv_first_emission:
  !env ty id a x b. compile_name_vv env ty id a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac (srw_ss()) [compile_name_vv_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp_tac (srw_ss()) []) >>
  FIRST [(simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl] >> NO_TAC),
    ho_match_mp_tac first_emission_strong >>
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
    >- (rpt gen_tac >> Cases_on `x` >> strip_tac >>
        irule (cj 1 first_emission_emit_helpers) >>
        goal_assum $ drule_at Any >> simp[]) >>
    rewrite_tac[GSYM cs_appends_def] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[cs_appends_return]]
QED

Theorem ctor_env_var_first_emission:
  !ev a x b. compile_env_var ev a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  Cases >> rewrite_tac[compile_env_var_def] >>
  FIRST [ho_match_mp_tac first_emission_strong_bind >> conj_tac
    >- (qspec_then `NUMBER` mp_tac (cj 3 first_emission_emit_helpers) >>
        simp[] >> metis_tac[]) >>
    gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
    ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers],
    rpt gen_tac >> strip_tac >>
    irule (cj 3 first_emission_emit_helpers) >>
    goal_assum $ drule_at Any >> simp[]]
QED

Theorem ctor_lower_value_first_emission:
  !cfn env ty e.
  (!a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !a x b. lower_value cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> strip_tac >> rewrite_tac[lower_value_def] >>
  ho_match_mp_tac first_emission_bind >>
  metis_tac[ctor_unwrap_value_first_emission]
QED

Theorem ctor_load_bytestring_as_word_appends:
  !v opc. cs_appends (load_bytestring_as_word v opc)
Proof
  rpt gen_tac >> rewrite_tac[load_bytestring_as_word_def] >>
  Cases_on `opc = SAR` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_int_clamp_appends:
  !signed bits v. cs_appends (compile_int_clamp signed bits v)
Proof
  rpt gen_tac >> Cases_on `signed` >>
  simp_tac (srw_ss()) [compile_int_clamp_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_type_convert_appends:
  !v cv. cs_appends (compile_type_convert v cv)
Proof
  gen_tac >> Cases >> simp_tac (srw_ss()) [compile_type_convert_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_load_bytestring_as_word_appends, ctor_int_clamp_appends]) >>
  simp[cs_appends_return, cs_appends_emit_helpers, ctor_int_clamp_appends] >>
  PairCases_on `a` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_int_clamp_appends]) >>
  simp[cs_appends_return, cs_appends_emit_helpers, ctor_int_clamp_appends]
QED

Theorem ctor_load_bytestring_as_word_first_emission:
  !v opc a x b. load_bytestring_as_word v opc a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[load_bytestring_as_word_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (qspec_then `MLOAD` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  Cases_on `opc = SAR` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_int_clamp_first_emission:
  !signed bits v a x b. compile_int_clamp signed bits v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> Cases_on `signed` >>
  simp_tac (srw_ss()) [compile_int_clamp_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (qspec_then `SLT` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[])
  >- (gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      rpt (FIRST [ho_match_mp_tac cs_appends_bind,
                  ho_match_mp_tac cs_appends_ignore_bind] >>
           rw[cs_appends_emit_helpers, cs_appends_return]))
  >- (qspec_then `GT` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_type_convert_first_emission:
  !v cv a x b. compile_type_convert v cv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> Cases >> simp_tac (srw_ss()) [compile_type_convert_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  let
    fun fe g = FIRST [
      (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl] >> NO_TAC),
      (ho_match_mp_tac first_emission_strong >>
       FIRST [
         (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC),
         (rpt gen_tac >> strip_tac >>
          rename1 `emit_void _ _ _ = (u,_)` >> Cases_on `u` >>
          irule (cj 2 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC),
         (rpt gen_tac >> strip_tac >>
          drule ctor_int_clamp_first_emission >> simp[] >> NO_TAC),
         (rpt gen_tac >> strip_tac >>
          drule ctor_load_bytestring_as_word_first_emission >> simp[] >> NO_TAC)]),
      (ho_match_mp_tac first_emission_bind >> conj_tac >> fe),
      (ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> fe),
      (IF_CASES_TAC >> simp[] >> fe),
      (gen_tac >> fe),
      (pairarg_tac >> gvs[] >>
       rename1 `_ s = (res,t)` >>
       map_every qid_spec_tac [`t`, `res`, `s`] >> fe)
    ] g
  in fe end
QED

Theorem ctor_clamp_appends:
  !v ty. cs_appends (compile_clamp v ty)
Proof
  rpt gen_tac >> rewrite_tac[compile_clamp_def] >>
  Cases_on `type_bounds ty` >> simp_tac (srw_ss()) [LET_THM] >> IF_CASES_TAC >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers]) >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_clamp_first_emission:
  !v ty a x b. compile_clamp v ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_clamp_def] >>
  Cases_on `type_bounds ty` >>
  pure_rewrite_tac [LET_THM] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >> IF_CASES_TAC >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (qspec_then `SLT` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[])
  >- (gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      rpt (ho_match_mp_tac cs_appends_bind >> rw[cs_appends_emit_helpers]) >>
      simp[cs_appends_emit_helpers])
  >- (qspec_then `GT` mp_tac (cj 3 first_emission_emit_helpers) >>
      simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_clamp_and_return_appends:
  !v ty. cs_appends (clamp_and_return v ty)
Proof
  rpt gen_tac >> rewrite_tac[clamp_and_return_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >>
  simp[ctor_clamp_appends, cs_appends_return]
QED

Theorem ctor_clamp_and_return_first_emission:
  !v ty a x b. clamp_and_return v ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> rewrite_tac[clamp_and_return_def] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[ctor_clamp_first_emission] >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_clamp_basetype_appends:
  !v ty. cs_appends (compile_clamp_basetype v ty)
Proof
  rpt gen_tac >> rewrite_tac[oneline compile_clamp_basetype_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  rpt IF_CASES_TAC >> simp[cs_appends_return, ctor_clamp_and_return_appends] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_clamp_basetype_first_emission:
  !v ty a x b. compile_clamp_basetype v ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> rewrite_tac[oneline compile_clamp_basetype_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> rpt IF_CASES_TAC >> simp[] >>
  FIRST [
    (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl] >> NO_TAC),
    (rpt gen_tac >> strip_tac >>
     drule ctor_clamp_and_return_first_emission >> simp[] >> NO_TAC),
    (ho_match_mp_tac first_emission_strong >>
     ho_match_mp_tac first_emission_strong_bind >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         irule (cj 3 first_emission_emit_helpers) >>
         goal_assum $ drule_at Any >> simp[]) >>
     gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
     rpt (FIRST [ho_match_mp_tac cs_appends_bind,
                 ho_match_mp_tac cs_appends_ignore_bind] >>
          rw[cs_appends_emit_helpers, cs_appends_return]))]
QED

Theorem ctor_mul_overflow_check_appends:
  !p q r signed bits.
    cs_appends (compile_mul_overflow_check p q r signed bits)
Proof
  rpt gen_tac >> Cases_on `signed` >>
  simp_tac (srw_ss()) [compile_mul_overflow_check_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  rpt IF_CASES_TAC >> simp[cs_appends_return, cs_appends_emit_helpers] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_mul_overflow_check_first_emission:
  !p q r signed bits a x b.
    compile_mul_overflow_check p q r signed bits a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> Cases_on `signed` >>
  pure_rewrite_tac [compile_mul_overflow_check_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[])
  >- (gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      rpt (FIRST [ho_match_mp_tac cs_appends_bind,
                  ho_match_mp_tac cs_appends_ignore_bind] >>
           rw[cs_appends_emit_helpers, cs_appends_return]) >>
      rpt IF_CASES_TAC >> simp[cs_appends_return, cs_appends_emit_helpers] >>
      rpt (FIRST [ho_match_mp_tac cs_appends_bind,
                  ho_match_mp_tac cs_appends_ignore_bind] >>
           rw[cs_appends_emit_helpers, cs_appends_return]))
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_safe_add_appends:
  !p q ty. cs_appends (compile_safe_add p q ty)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_safe_add_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_clamp_and_return_appends])
QED

Theorem ctor_safe_sub_appends:
  !p q ty. cs_appends (compile_safe_sub p q ty)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_safe_sub_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_clamp_and_return_appends])
QED

Theorem ctor_safe_mul_appends:
  !p q ty. cs_appends (compile_safe_mul p q ty)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_safe_mul_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_mul_overflow_check_appends, ctor_clamp_and_return_appends])
QED

Theorem ctor_safe_div_appends:
  !p q ty. cs_appends (compile_safe_div p q ty)
Proof
  rpt gen_tac >> rewrite_tac[compile_safe_div_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_clamp_and_return_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_clamp_and_return_appends]
QED

Theorem ctor_safe_decimal_div_appends:
  !p q divisor ty. cs_appends (compile_safe_decimal_div p q divisor ty)
Proof
  rpt gen_tac >> rewrite_tac[compile_safe_decimal_div_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_clamp_and_return_appends])
QED

Theorem ctor_safe_mod_appends:
  !p q ty. cs_appends (compile_safe_mod p q ty)
Proof
  rpt gen_tac >> rewrite_tac[compile_safe_mod_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_safe_add_first_emission:
  !p q ty a x b. compile_safe_add p q ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac (srw_ss()) [compile_safe_add_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt IF_CASES_TAC >> simp[ctor_clamp_and_return_appends] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_safe_sub_first_emission:
  !p q ty a x b. compile_safe_sub p q ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac (srw_ss()) [compile_safe_sub_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt IF_CASES_TAC >> simp[ctor_clamp_and_return_appends] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_safe_mul_first_emission:
  !p q ty a x b. compile_safe_mul p q ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac (srw_ss()) [compile_safe_mul_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_mul_overflow_check_appends, ctor_clamp_and_return_appends])
QED

Theorem ctor_safe_div_first_emission:
  !p q ty a x b. compile_safe_div p q ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_safe_div_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_clamp_and_return_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_clamp_and_return_appends]
QED

Theorem ctor_safe_decimal_div_first_emission:
  !p q divisor ty a x b. compile_safe_decimal_div p q divisor ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> rewrite_tac[compile_safe_decimal_div_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_clamp_and_return_appends])
QED

Theorem ctor_safe_mod_first_emission:
  !p q ty a x b. compile_safe_mod p q ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_safe_mod_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_neg_appends:
  !v ty. cs_appends (compile_neg v ty)
Proof
  rpt gen_tac >> rewrite_tac[compile_neg_def] >>
  Cases_on `type_bounds ty` >> simp_tac (srw_ss()) [LET_THM] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers]) >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_neg_first_emission:
  !v ty a x b. compile_neg v ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_neg_def] >>
  Cases_on `type_bounds ty` >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers]) >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_safe_pow_appends:
  !p q ty base_literal exp_literal.
    cs_appends (compile_safe_pow p q ty base_literal exp_literal)
Proof
  rpt gen_tac >> Cases_on `base_literal` >> Cases_on `exp_literal` >>
  simp_tac (srw_ss()) [compile_safe_pow_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_clamp_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_safe_pow_first_emission:
  !p q ty base_literal exp_literal a x b.
    compile_safe_pow p q ty base_literal exp_literal a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> Cases_on `base_literal` >> Cases_on `exp_literal` >>
  simp_tac (srw_ss()) [compile_safe_pow_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  let
    fun fe g = FIRST [
      (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl] >> NO_TAC),
      (rpt gen_tac >> strip_tac >>
       drule ctor_clamp_first_emission >> simp[] >> NO_TAC),
      (ho_match_mp_tac first_emission_strong >>
       FIRST [
         (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC),
         (rpt gen_tac >> strip_tac >>
          rename1 `emit_void _ _ _ = (u,_)` >> Cases_on `u` >>
          irule (cj 2 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC)]),
      (ho_match_mp_tac first_emission_bind >> conj_tac >> fe),
      (ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> fe),
      (IF_CASES_TAC >> simp[] >> fe),
      (gen_tac >> fe)
    ] g
  in fe end
QED

Theorem ctor_compare_appends:
  !op p q ty. cs_appends (compile_compare op p q ty)
Proof
  Cases >> rpt gen_tac >>
  simp_tac (srw_ss()) [compile_compare_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[cs_appends_emit_helpers] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem ctor_compare_first_emission:
  !op p q ty a x b. compile_compare op p q ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  Cases >> ntac 3 gen_tac >>
  simp_tac (srw_ss()) [compile_compare_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  let
    fun fe g = FIRST [
      (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl] >> NO_TAC),
      (ho_match_mp_tac first_emission_strong >>
       FIRST [
         (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC),
         (rpt gen_tac >> strip_tac >>
          rename1 `emit_inst _ _ _ _ = (u,_)` >> Cases_on `u` >>
          irule (cj 1 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC)]),
      (ho_match_mp_tac first_emission_bind >> conj_tac >> fe),
      (ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> fe),
      (gen_tac >> fe)
    ] g
  in fe end
QED

Theorem ctor_bytestring_hash_appends:
  !ptr_op. cs_appends (compile_bytestring_hash ptr_op)
Proof
  gen_tac >> rewrite_tac[compile_bytestring_hash_def] >>
  rpt (ho_match_mp_tac cs_appends_bind >> rw[cs_appends_emit_helpers]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_bytestring_hash_first_emission:
  !ptr_op a x b. compile_bytestring_hash ptr_op a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> rewrite_tac[compile_bytestring_hash_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_mapping_subscript_appends:
  !base_slot key_op. cs_appends (compile_mapping_subscript base_slot key_op)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_mapping_subscript_def, LET_THM] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (rw[cs_appends_def] >> metis_tac[ctor_alloc_buffer_first_emission]) >>
  gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers]) >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_mapping_subscript_first_emission:
  !base_slot key_op a x b. compile_mapping_subscript base_slot key_op a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >>
  simp_tac (srw_ss()) [compile_mapping_subscript_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers]) >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_keccak256_key_appends:
  !key_op is_bytes32. cs_appends (compile_keccak256_key key_op is_bytes32)
Proof
  gen_tac >> Cases >>
  simp_tac (srw_ss()) [compile_keccak256_key_def, LET_THM] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (rw[cs_appends_def] >> metis_tac[ctor_alloc_buffer_first_emission])
  >- (gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> simp[cs_appends_emit_helpers])
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_keccak256_key_first_emission:
  !key_op is_bytes32 a x b. compile_keccak256_key key_op is_bytes32 a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> Cases >>
  simp_tac (srw_ss()) [compile_keccak256_key_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission]
  >- (gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_ignore_bind >> simp[cs_appends_emit_helpers])
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_wrap_truncate_appends:
  !res ty. cs_appends (wrap_truncate res ty)
Proof
  rpt gen_tac >> rewrite_tac[wrap_truncate_def] >>
  rpt IF_CASES_TAC >> simp[cs_appends_return, cs_appends_emit_helpers]
QED

Theorem ctor_wrap_truncate_first_emission:
  !res ty a x b. wrap_truncate res ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> rewrite_tac[wrap_truncate_def] >> rpt IF_CASES_TAC >>
  FIRST [
    (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl] >> NO_TAC),
    (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
     irule (cj 3 first_emission_emit_helpers) >>
     goal_assum $ drule_at Any >> simp[])]
QED

Theorem ctor_select_appends[local]:
  !c p q. cs_appends (compile_select c p q)
Proof
  rpt gen_tac >> rewrite_tac[builtinSimpleTheory.compile_select_def] >>
  rpt (ho_match_mp_tac cs_appends_bind >> rw[cs_appends_emit_helpers]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_binop_appends:
  !op p q ty base_literal exp_literal.
    cs_appends (compile_binop op p q ty base_literal exp_literal)
Proof
  Cases >> rpt gen_tac >> simp_tac (srw_ss()) [compile_binop_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  simp[ctor_safe_add_appends, ctor_safe_sub_appends, ctor_safe_mul_appends,
       ctor_safe_div_appends, ctor_safe_decimal_div_appends, ctor_safe_mod_appends,
       ctor_safe_pow_appends, ctor_compare_appends, cs_appends_emit_helpers] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          ctor_wrap_truncate_appends, ctor_select_appends])
QED

Theorem ctor_binop_first_emission:
  !op p q ty base_literal exp_literal a x b.
    compile_binop op p q ty base_literal exp_literal a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  Cases >> ntac 5 gen_tac >> simp_tac (srw_ss()) [compile_binop_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  FIRST [
    (rpt gen_tac >> strip_tac >>
     FIRST (map drule [ctor_safe_add_first_emission, ctor_safe_sub_first_emission,
       ctor_safe_mul_first_emission, ctor_safe_div_first_emission,
       ctor_safe_decimal_div_first_emission, ctor_safe_mod_first_emission,
       ctor_safe_pow_first_emission, ctor_compare_first_emission]) >> simp[] >> NO_TAC),
    (ho_match_mp_tac first_emission_strong >>
     let
       val primitive = FIRST [
         (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC),
         (rpt gen_tac >> strip_tac >>
          rename1 `emit_inst _ _ _ _ = (u,_)` >> Cases_on `u` >>
          irule (cj 1 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[] >> NO_TAC)]
     in
       FIRST [primitive,
         (FIRST [ho_match_mp_tac first_emission_strong_bind,
                 ho_match_mp_tac first_emission_strong_ignore_bind] >> conj_tac
          >- primitive >>
          rewrite_tac[GSYM cs_appends_def] >> rpt gen_tac >>
          rpt (FIRST [ho_match_mp_tac cs_appends_bind,
                      ho_match_mp_tac cs_appends_ignore_bind] >>
               rw[cs_appends_emit_helpers, cs_appends_return,
                  ctor_wrap_truncate_appends, ctor_select_appends]) >>
          simp[cs_appends_emit_helpers, cs_appends_return,
               ctor_wrap_truncate_appends, ctor_select_appends])]
     end)]
QED

Theorem ctor_emit_membership_eqs_appends:
  !needle elems. cs_appends (emit_membership_eqs needle elems)
Proof
  gen_tac >> Induct >> simp[emit_membership_eqs_def, cs_appends_return] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_return]
QED

Theorem ctor_fold_membership_or_appends:
  !cs acc. cs_appends (fold_membership_or acc cs)
Proof
  Induct >> simp[fold_membership_or_def, cs_appends_return] >>
  rpt gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_fold_membership_and_appends:
  !cs acc. cs_appends (fold_membership_and acc cs)
Proof
  Induct >> simp[fold_membership_and_def, cs_appends_return] >>
  rpt gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_list_membership_in_appends:
  !needle elems. cs_appends (compile_list_membership_in needle elems)
Proof
  rpt gen_tac >> rewrite_tac[compile_list_membership_in_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[ctor_emit_membership_eqs_appends] >>
  Cases >> simp[cs_appends_return, ctor_fold_membership_or_appends]
QED

Theorem ctor_list_membership_notin_appends:
  !needle elems. cs_appends (compile_list_membership_notin needle elems)
Proof
  rpt gen_tac >> rewrite_tac[compile_list_membership_notin_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[ctor_emit_membership_eqs_appends] >>
  Cases >> simp[cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >>
  simp[cs_appends_emit_helpers, ctor_fold_membership_and_appends]
QED

Theorem ctor_emit_membership_eqs_cons_first_emission[local]:
  !needle h t a x b. emit_membership_eqs needle (h::t) a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[emit_membership_eqs_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >>
  simp[ctor_emit_membership_eqs_appends, cs_appends_return]
QED

Theorem ctor_list_membership_in_first_emission:
  !needle elems a x b. compile_list_membership_in needle elems a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> Cases
  >- (simp[compile_list_membership_in_def, emit_membership_eqs_def,
           comp_bind_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl]) >>
  rewrite_tac[compile_list_membership_in_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC ctor_emit_membership_eqs_cons_first_emission >>
  Cases >> rewrite_tac[GSYM cs_appends_def] >>
  simp[cs_appends_return, ctor_fold_membership_or_appends]
QED

Theorem ctor_list_membership_notin_first_emission:
  !needle elems a x b. compile_list_membership_notin needle elems a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> Cases
  >- (simp[compile_list_membership_notin_def, emit_membership_eqs_def,
           comp_bind_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl]) >>
  rewrite_tac[compile_list_membership_notin_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC ctor_emit_membership_eqs_cons_first_emission >>
  Cases >> rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >>
  simp[cs_appends_emit_helpers, ctor_fold_membership_and_appends]
QED

Theorem ctor_first_emission_weak_strong_bind[local]:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c /\
    (!fn. fn_has_code b c fn ==> ?bb i.
      lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (b.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)) ==>
  !a y c. comp_bind m k a = (y,c) ==> cs_extends a c /\
    (!fn. fn_has_code a c fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  strip_tac >> rpt gen_tac >> simp_tac bool_ss [comp_bind_def] >>
  Cases_on `m a` >> rename1 `m a = (x,b)` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  first_x_assum drule >> disch_then assume_tac >>
  first_x_assum drule >> disch_then assume_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  gvs[] >> rpt strip_tac >> drule_all fn_has_code_split >>
  strip_tac >> metis_tac[]
QED

Theorem ctor_tuple_subscript_first_emission:
  !base off a x b. compile_tuple_subscript base off a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_tuple_subscript_def] >> rpt gen_tac >> strip_tac >>
  irule (cj 3 first_emission_emit_helpers) >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem ctor_array_membership_loop_appends:
  !loader. (!op. cs_appends (loader op)) ==>
  !needle arr len size off bnd is_in.
    cs_appends (compile_array_membership_loop needle arr len size off loader bnd is_in)
Proof
  rpt strip_tac >> Cases_on `bnd` >>
  rewrite_tac[compile_array_membership_loop_def, optionTheory.option_case_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_array_membership_loop_first_emission:
  !loader. (!op. cs_appends (loader op)) ==>
  !needle arr len size off bnd is_in a x b.
    compile_array_membership_loop needle arr len size off loader bnd is_in a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI)
Proof
  gen_tac >> strip_tac >> ntac 5 gen_tac >> Cases >> gen_tac >>
  rewrite_tac[compile_array_membership_loop_def, optionTheory.option_case_def] >>
  ntac 7 (ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
    >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `x` >>
      irule (cj 1 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_array_subscript_appends:
  !loader. (!op. cs_appends (loader op)) ==>
  !base idx dyn count scale size signed.
    cs_appends (compile_array_subscript base idx dyn count scale size signed loader)
Proof
  rpt strip_tac >> rewrite_tac[compile_array_subscript_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_array_subscript_first_emission:
  !loader.
  (!op a x b. loader op a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !base idx dyn count scale size signed a x b.
    compile_array_subscript base idx dyn count scale size signed loader a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI)
Proof
  gen_tac >> strip_tac >> ntac 7 gen_tac >>
  rewrite_tac[compile_array_subscript_def] >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[first_emission_return]) >>
  gen_tac >> ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (IF_CASES_TAC >- (ho_match_mp_tac first_emission_strong >>
        rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
        goal_assum $ drule_at Any >> simp[]) >>
      metis_tac[first_emission_return]) >>
  gen_tac >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> rpt gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_var_array_membership_appends:
  !env needle arr ty is_in.
    cs_appends (compile_var_array_membership env needle arr ty is_in)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_var_array_membership_def, LET_THM] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ctor_ptr_load_appends] >>
      Cases_on `ty` >> simp[cs_appends_return] >>
      rename1 `ArrayT _ bound` >> Cases_on `bound` >> simp[cs_appends_return]) >>
  simp[ctor_array_membership_loop_appends, ctor_ptr_load_appends]
QED

Theorem ctor_var_array_membership_first_emission:
  !env needle arr ty is_in a x b.
    compile_var_array_membership env needle arr ty is_in a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI)
Proof
  ntac 5 gen_tac >>
  simp_tac (srw_ss()) [compile_var_array_membership_def, LET_THM] >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_strong >>
          metis_tac[ctor_ptr_load_first_emission]) >>
      Cases_on `ty` >> simp[] >>
      FIRST [metis_tac[first_emission_return],
        (rename1 `ArrayT _ bound` >> Cases_on `bound` >> simp[] >>
         metis_tac[first_emission_return])]) >>
  metis_tac[ctor_array_membership_loop_first_emission, ctor_ptr_load_appends]
QED

Theorem ctor_dynarray_pop_first_emission:
  !base scale size is_ctor imm loc a x b.
    compile_dynarray_pop base scale size is_ctor imm loc a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 6 gen_tac >>
  simp_tac (srw_ss()) [compile_dynarray_pop_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_ptr_load_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, ctor_ptr_store_appends]) >>
  simp[cs_appends_emit_helpers, ctor_ptr_store_appends]
QED

Theorem ctor_builtin_len_first_emission_strong:
  !is_ctor imm ptr loc a x b.
    compile_builtin_len is_ctor imm ptr loc a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_builtin_len_def] >>
  metis_tac[ctor_ptr_load_first_emission]
QED

Theorem ctor_builtin_calldatasize_first_emission_strong:
  !a x b. compile_builtin_calldatasize a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_builtin_calldatasize_def] >>
  rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem ctor_pow_mod256_first_emission_strong:
  !base ex a x b. compile_pow_mod256 base ex a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_pow_mod256_def] >>
  rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem ctor_blobhash_first_emission_strong:
  !n a x b. compile_blobhash n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  rewrite_tac[compile_blobhash_def] >>
  rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem ctor_invert_first_emission_strong:
  !v ty env a x b. compile_invert v ty env a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> Cases >> rewrite_tac[compile_invert_def, LET_THM] >>
  FIRST [
    (qspec_then `NOT` mp_tac (cj 3 first_emission_emit_helpers) >>
     simp[] >> metis_tac[]),
    (qspec_then `XOR` mp_tac (cj 3 first_emission_emit_helpers) >>
     simp[] >> metis_tac[])]
QED

Theorem ctor_builtin_abs_first_emission_strong:
  !v a x b. compile_builtin_abs v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_builtin_abs_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, ctor_select_appends]) >>
  simp[cs_appends_emit_helpers, ctor_select_appends]
QED

Theorem ctor_addmod_first_emission_strong:
  !u v w a x b. compile_addmod u v w a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_addmod_def, comp_ignore_bind_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 2 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_mulmod_first_emission_strong:
  !u v w a x b. compile_mulmod u v w a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_mulmod_def, comp_ignore_bind_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 2 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_blockhash_first_emission_strong:
  !n a x b. compile_blockhash n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_blockhash_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers]) >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_floor_first_emission_strong:
  !v d a x b. compile_floor v d a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_floor_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (ho_match_mp_tac cs_appends_bind >>
       rw[cs_appends_emit_helpers, ctor_select_appends]) >>
  simp[cs_appends_emit_helpers, ctor_select_appends]
QED

Theorem ctor_ceil_first_emission_strong:
  !v d a x b. compile_ceil v d a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_ceil_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (ho_match_mp_tac cs_appends_bind >>
       rw[cs_appends_emit_helpers, ctor_select_appends]) >>
  simp[cs_appends_emit_helpers, ctor_select_appends]
QED

Theorem ctor_zero_words_appends:
  !base n. cs_appends (compile_zero_words base n)
Proof
  gen_tac >> Induct >> rewrite_tac[compile_zero_words_def] >>
  simp[cs_appends_return] >>
  ho_match_mp_tac cs_appends_ignore_bind >> simp[] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_builtin_empty_complex_first_emission_strong:
  !size bs a x b. compile_builtin_empty_complex size bs a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_builtin_empty_complex_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_return] >>
  gen_tac >> IF_CASES_TAC >> simp[LET_THM] >>
  ho_match_mp_tac cs_appends_ignore_bind >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_zero_words_appends]
QED

Theorem ctor_acc_first_emission:
  !cfn env e.
  (!a x b. lower_value cfn env (BaseT AddressT) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !accessor a x b. compile_acc cfn env e accessor a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> strip_tac >> Cases >>
  rewrite_tac[compile_acc_def, LET_THM, state_pair_let_bind] >>
  FIRST [
    (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[] >> gen_tac >>
     ho_match_mp_tac first_emission_strong >>
     FIRST [
       (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
        goal_assum $ drule_at Any >> simp[]),
       (ho_match_mp_tac first_emission_strong_bind >> conj_tac
        >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
            goal_assum $ drule_at Any >> simp[]) >>
        rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers])]),
    (metis_tac[]),
    (ho_match_mp_tac first_emission_bind >> conj_tac
     >- (ho_match_mp_tac first_emission_strong >>
         rpt gen_tac >> strip_tac >> irule (cj 1 first_emission_emit_helpers) >>
         goal_assum $ drule_at Any >> simp[]) >>
     simp[first_emission_return, cs_extends_refl])]
QED

Theorem ctor_alloc_buffer_appends[local]:
  !size. cs_appends (compile_alloc_buffer size)
Proof
  rw[cs_appends_def] >> metis_tac[ctor_alloc_buffer_first_emission]
QED

Theorem ctor_keccak256_word_first_emission_strong:
  !v a x b. compile_keccak256_word v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_keccak256_word_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_keccak256_bytes_first_emission_strong:
  !v a x b. compile_keccak256_bytes v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_keccak256_bytes_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_keccak256_bytesm_first_emission_strong:
  !v m a x b. compile_keccak256_bytesm v m a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_keccak256_bytesm_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_sha256_word_first_emission_strong:
  !v a x b. compile_sha256_word v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_sha256_word_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_sha256_bytes_first_emission_strong:
  !v a x b. compile_sha256_bytes v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_sha256_bytes_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_sha256_bytesm_first_emission_strong:
  !v m a x b. compile_sha256_bytesm v m a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_sha256_bytesm_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_method_id_hash_first_emission_strong:
  !ty v a x b. compile_method_id_hash ty v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  Cases >> rewrite_tac[compile_method_id_hash_def] >>
  FIRST [metis_tac[ctor_keccak256_bytes_first_emission_strong],
    (rename1 `BaseT bt` >> Cases_on `bt` >> rewrite_tac[compile_method_id_hash_def] >>
     FIRST [metis_tac[ctor_keccak256_bytes_first_emission_strong],
       (rename1 `BytesT bd` >> Cases_on `bd` >>
        rewrite_tac[compile_method_id_hash_def] >>
        metis_tac[ctor_keccak256_bytes_first_emission_strong,
                  ctor_keccak256_bytesm_first_emission_strong])])]
QED

Theorem ctor_method_id_runtime_first_emission_strong:
  !ty v bs a x b. compile_method_id_runtime ty v bs a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_method_id_runtime_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_method_id_hash_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  ntac 2 (ho_match_mp_tac cs_appends_bind >>
          simp[cs_appends_emit_helpers] >> gen_tac) >>
  IF_CASES_TAC >> simp[cs_appends_return] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_assert_slice_bounds_first_emission_strong:
  !s l n a x b. compile_assert_slice_bounds s l n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_assert_slice_bounds_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (ho_match_mp_tac cs_appends_bind >> rw[cs_appends_emit_helpers]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_assert_slice_bounds_appends:
  !s l n. cs_appends (compile_assert_slice_bounds s l n)
Proof
  rw[cs_appends_def] >> metis_tac[ctor_assert_slice_bounds_first_emission_strong]
QED

Theorem ctor_bytestring_src_first_emission_strong:
  !p a x b. compile_bytestring_src p a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_bytestring_src_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_slice_out_buf_first_emission_strong:
  !size a x b. compile_slice_out_buf size a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_slice_out_buf_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (ho_match_mp_tac cs_appends_bind >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_return]
QED

Theorem ctor_slice_data_first_emission_strong:
  !n p s l size a x b. compile_slice_data n p s l size a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 5 gen_tac >> rewrite_tac[compile_slice_data_def, comp_ignore_bind_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_assert_slice_bounds_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (ho_match_mp_tac cs_appends_bind >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_slice_extcode_first_emission_strong:
  !addr s l p d a x b. compile_slice_extcode addr s l p d a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 5 gen_tac >> rewrite_tac[compile_slice_extcode_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_assert_slice_bounds_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_extract32_load_first_emission_strong:
  !n p s a x b. compile_extract32_load n p s a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_extract32_load_def, comp_ignore_bind_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_assert_slice_bounds_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_slice_calldata_first_emission_strong:
  !s l size a x b. compile_slice_calldata s l size a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_slice_calldata_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_slice_out_buf_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  pairarg_tac >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_assert_slice_bounds_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_slice_code_first_emission_strong:
  !s l size a x b. compile_slice_code s l size a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_slice_code_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_slice_out_buf_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  pairarg_tac >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_assert_slice_bounds_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_ecrecover_first_emission_strong:
  !h v r s a x b. compile_ecrecover h v r s a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 4 gen_tac >> rewrite_tac[compile_ecrecover_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_ecadd_points_first_emission_strong:
  !p q a x b. compile_ecadd_points p q a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_ecadd_points_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_ecmul_point_first_emission_strong:
  !p scalar a x b. compile_ecmul_point p scalar a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_ecmul_point_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]) >>
  simp[cs_appends_emit_helpers, cs_appends_return, ctor_alloc_buffer_appends]
QED

Theorem ctor_invalid_callback_first_emission:
  !ty a x b. invalid_expr_call ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  gen_tac >> simp_tac (srw_ss()) [exprCallBoundsTheory.invalid_expr_call_def,
    LET_THM] >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >> Cases_on `x` >>
      irule (cj 1 first_emission_emit_helpers) >>
      qexistsl [`INVALID`, `[]`, `[]`] >> simp[]) >>
  simp[cs_extends_refl]
QED

Theorem ctor_expr_callback_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env ty e a x b. expr_child_callback bound cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `expr_size e < bound` >>
  simp[exprCallBoundsTheory.expr_child_callback_def] >>
  metis_tac[ctor_invalid_callback_first_emission]
QED

Theorem ctor_builtin_callback_first_emission:
  (!args env rt ty bi a.
    list_size expr_size args < bound ==> !x b. dispatch env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty bi args a x b.
    builtin_child_callback bound dispatch env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `list_size expr_size args < bound` >>
  simp[exprCallBoundsTheory.builtin_child_callback_def] >>
  metis_tac[ctor_invalid_callback_first_emission]
QED

Theorem ctor_type_callback_first_emission:
  (!args env vt ty tb rt a.
    list_size expr_size args < bound ==> !x b. dispatch env vt ty tb rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env vt ty tb rt args a x b.
    type_child_callback bound dispatch env vt ty tb rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `list_size expr_size args < bound` >>
  simp[exprCallBoundsTheory.type_child_callback_def] >>
  metis_tac[ctor_invalid_callback_first_emission]
QED

Theorem ctor_len_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty args a x b.
    compile_builtin_dispatch_body cfn env rt ty Len args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `as_stack_val rt m` >>
  Cases_on `m` >> simp[as_stack_val_def] >> strip_tac >> gvs[] >>
  drule ctor_builtin_len_first_emission_strong >> metis_tac[]
QED

Theorem ctor_ci_mono_appends:
  (!a. ci_mono a (SND (m a))) ==> cs_appends m
Proof
  simp[ci_mono_def, cs_appends_def] >> metis_tac[pairTheory.SND]
QED

Theorem ctor_ifexp_arm_appends:
  !env rt ty v. cs_appends (compile_ifexp_arm env rt ty v)
Proof
  rpt gen_tac >> irule ctor_ci_mono_appends >>
  simp[ci_mono_compile_ifexp_arm]
QED

Theorem ctor_expr_callback_ci_mono:
  !bound env ty e a.
    ci_mono a (SND (expr_child_callback bound compile_expr env ty e a))
Proof
  gen_tac >> irule ci_mono_expr_child_callback >>
  rpt gen_tac >> disch_tac >>
  Cases_on `compile_expr ce ty e st` >>
  drule compile_expr_extends >> simp[ci_mono_def]
QED

Theorem ctor_expr_callback_appends:
  !bound env ty e.
    cs_appends (expr_child_callback bound compile_expr env ty e)
Proof
  rpt gen_tac >> irule ctor_ci_mono_appends >>
  simp[ctor_expr_callback_ci_mono]
QED

Theorem ctor_guarded_ifexp_first_emission:
  (!e env ty a. expr_size e < expr_size (IfExp ann cond yes no) ==>
    !x b. compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !a x b.
    compile_expr_body
      (expr_child_callback (expr_size (IfExp ann cond yes no)) compile_expr)
      cb ct env ty (IfExp ann cond yes no) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  ho_match_mp_tac ctor_ifexp_first_emission >>
  simp_tac bool_ss [ctor_expr_callback_appends, ctor_ifexp_arm_appends] >>
  ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]
QED

Theorem ctor_as_stack_val_first_emission[local]:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !a x b. as_stack_val rt (m a) = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ctor_as_ptr_val_first_emission[local]:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !a x b. as_ptr_val rt loc (m a) = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ctor_not_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty args a x b.
    compile_builtin_dispatch_body cfn env rt ty Not args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac
  >- (irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  drule ctor_invert_first_emission_strong >> simp[]
QED

Theorem ctor_scalar_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty bi args.
    (bi = Not \/ bi = Neg \/ bi = Abs \/ (?item. bi = Env item) \/
     (?item. bi = Acc item) \/ bi = Keccak256 \/ bi = Sha256 \/
     bi = CalldataLen \/ (?n. bi = CalldataSlice n) \/ bi = Len \/
     bi = BlockHash \/ bi = BlobHash \/ bi = AddMod \/ bi = MulMod \/
     bi = Ceil \/ bi = Floor \/ bi = PowMod256) ==>
  !a x b. compile_builtin_dispatch_body cfn env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >> strip_tac >> gvs[]
  >- (drule ctor_not_dispatch_first_emission >>
      disch_then (qspecl_then [`env`, `rt`, `ty`, `args`] ACCEPT_TAC))
  >- suspend "neg"
  >- suspend "abs"
  >- suspend "env"
  >- suspend "acc"
  >- suspend "keccak"
  >- suspend "sha"
  >- suspend "cdlen"
  >- suspend "cdslice"
  >- (drule ctor_len_dispatch_first_emission >>
      disch_then (qspecl_then [`env`, `rt`, `ty`, `args`] ACCEPT_TAC))
  >- suspend "blockhash"
  >- suspend "blobhash"
  >- suspend "addmod"
  >- suspend "mulmod"
  >- suspend "ceil"
  >- suspend "floor"
  >> suspend "powmod"
QED

Resume ctor_scalar_dispatch_first_emission[neg]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  rpt gen_tac >> disch_tac >> drule ctor_neg_first_emission >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[abs]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_builtin_abs_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[env]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  rpt gen_tac >> disch_tac >> drule ctor_env_var_first_emission >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[acc]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  rpt gen_tac >> disch_tac >> drule_at Any ctor_acc_first_emission >>
  (impl_tac >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[])) >>
  simp[]
QED

Resume ctor_scalar_dispatch_first_emission[cdlen]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_builtin_calldatasize_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[cdslice]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_slice_calldata_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[blockhash]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_blockhash_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[blobhash]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_blobhash_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[ceil]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_ceil_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[floor]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_floor_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[addmod]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_addmod_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[mulmod]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_mulmod_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[powmod]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_pow_mod256_first_emission_strong >> simp[]
QED

Resume ctor_scalar_dispatch_first_emission[keccak]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `is_bytestring_type (expr_type (HD args))`
  >- (simp[] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule ctor_keccak256_bytes_first_emission_strong >> simp[]) >>
  simp[] >> Cases_on `expr_type (HD args)` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp[]) >>
  (rewrite_tac[state_pair_let_bind] >>
   ho_match_mp_tac first_emission_bind >> conj_tac
   >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
   gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
   ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
   FIRST [drule ctor_keccak256_bytesm_first_emission_strong >> simp[],
          drule ctor_keccak256_word_first_emission_strong >> simp[]])
QED

Resume ctor_scalar_dispatch_first_emission[sha]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `is_bytestring_type (expr_type (HD args))`
  >- (simp[] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule ctor_sha256_bytes_first_emission_strong >> simp[]) >>
  simp[] >> Cases_on `expr_type (HD args)` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp[]) >>
  (rewrite_tac[state_pair_let_bind] >>
   ho_match_mp_tac first_emission_bind >> conj_tac
   >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
   gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
   ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
   FIRST [drule ctor_sha256_bytesm_first_emission_strong >> simp[],
          drule ctor_sha256_word_first_emission_strong >> simp[]])
QED

Finalise ctor_scalar_dispatch_first_emission

Theorem ctor_guarded_scalar_dispatch_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty bi args.
    (bi = Not \/ bi = Neg \/ bi = Abs \/ (?item. bi = Env item) \/
     (?item. bi = Acc item) \/ bi = Keccak256 \/ bi = Sha256 \/
     bi = CalldataLen \/ (?n. bi = CalldataSlice n) \/ bi = Len \/
     bi = BlockHash \/ bi = BlobHash \/ bi = AddMod \/ bi = MulMod \/
     bi = Ceil \/ bi = Floor \/ bi = PowMod256) ==>
  !a x b. compile_builtin_dispatch_body
    (expr_child_callback bound compile_expr) env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >>
  disch_tac >> drule ctor_scalar_dispatch_first_emission >>
  disch_tac >> rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_bytes_precompile_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty bi args.
    (bi = ECRecover \/ bi = ECAdd \/ bi = ECMul \/ bi = MethodId \/
     (?n. bi = Slice n)) ==>
  !a x b. compile_builtin_dispatch_body cfn env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >> strip_tac >> gvs[]
  >- suspend "recover"
  >- suspend "add"
  >- suspend "mul"
  >- suspend "method"
  >> suspend "slice"
QED

Resume ctor_bytes_precompile_dispatch_first_emission[recover]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_ecrecover_first_emission_strong >> simp[]
QED

Resume ctor_bytes_precompile_dispatch_first_emission[add]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_ecadd_points_first_emission_strong >> simp[]
QED

Resume ctor_bytes_precompile_dispatch_first_emission[mul]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_ecmul_point_first_emission_strong >> simp[]
QED

Resume ctor_bytes_precompile_dispatch_first_emission[method]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `method_id_literal (HD args)` >> simp[]
  >- (rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> Cases_on `rt = BaseT (BytesT (Fixed 4))` >> simp[] >>
      FIRST [ho_match_mp_tac ctor_as_stack_val_first_emission,
             ho_match_mp_tac ctor_as_ptr_val_first_emission] >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule ctor_method_id_runtime_first_emission_strong >> simp[]) >>
  metis_tac[ctor_literal_vv_first_emission]
QED

Resume ctor_bytes_precompile_dispatch_first_emission[slice]:
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `is_msg_data (HD args)`
  >- (simp[] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule ctor_slice_calldata_first_emission_strong >> simp[]) >>
  Cases_on `is_self_code (HD args)`
  >- (simp[] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule ctor_slice_code_first_emission_strong >> simp[]) >>
  Cases_on `is_extcode (HD args)`
  >- (simp[] >> suspend "slice_ext") >>
  simp[] >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[]
  >- suspend "slice_bytes"
  >> suspend "slice_fixed"
QED

Resume ctor_bytes_precompile_dispatch_first_emission[slice_ext]:
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[ctor_slice_out_buf_first_emission_strong]) >>
  gen_tac >> pairarg_tac >> simp[] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_slice_extcode_first_emission_strong >> simp[]
QED

Resume ctor_bytes_precompile_dispatch_first_emission[slice_bytes]:
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[ctor_bytestring_src_first_emission_strong]) >>
  gen_tac >> pairarg_tac >> simp[] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_slice_data_first_emission_strong >> simp[]
QED

Resume ctor_bytes_precompile_dispatch_first_emission[slice_fixed]:
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[ctor_alloc_buffer_first_emission]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      irule (cj 2 first_emission_emit_helpers) >>
      goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  drule ctor_slice_data_first_emission_strong >> simp[]
QED

Finalise ctor_bytes_precompile_dispatch_first_emission

Theorem ctor_guarded_bytes_precompile_dispatch_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty bi args.
    (bi = ECRecover \/ bi = ECAdd \/ bi = ECMul \/ bi = MethodId \/
     (?n. bi = Slice n)) ==>
  !a x b. compile_builtin_dispatch_body
    (expr_child_callback bound compile_expr) env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >>
  disch_tac >> drule ctor_bytes_precompile_dispatch_first_emission >>
  disch_tac >> rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_multi_exprs_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env es a x b. compile_multi_exprs cfn env es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> gen_tac >> Induct >>
  simp_tac (srw_ss()) [Once compile_multi_exprs_def, LET_THM]
  >- (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_bop_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty op args a x b.
    compile_builtin_dispatch_body cfn env rt ty (Bop op) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))`
  >- (simp[] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> suspend "membership") >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ (op = Eq \/ op = NotEq)`
  >- (simp[] >> suspend "bytes_eq") >>
  simp[] >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  rpt gen_tac >> disch_tac >> drule ctor_binop_first_emission >> simp[]
QED

Resume ctor_bop_dispatch_first_emission[membership]:
  Cases_on `HD (TL args)` >> simp[] >>
  TRY (rename1 `Builtin et bi elems` >> Cases_on `bi` >> simp[]) >>
  (ho_match_mp_tac first_emission_bind >> conj_tac
   >- FIRST [(rpt gen_tac >> disch_tac >> first_x_assum drule >> simp[] >> NO_TAC),
             (drule ctor_multi_exprs_first_emission >>
              disch_then (qspecl_then [`env`, `elems`] ACCEPT_TAC))] >>
   gen_tac >>
   FIRST [(ho_match_mp_tac ctor_as_stack_val_first_emission >>
           rpt gen_tac >> disch_tac >>
           drule ctor_var_array_membership_first_emission >> simp[] >> NO_TAC),
          (Cases_on `op = In` >> simp[] >>
           ho_match_mp_tac ctor_as_stack_val_first_emission >>
           rpt gen_tac >> disch_tac >>
           FIRST [drule ctor_list_membership_in_first_emission >> simp[],
                  drule ctor_list_membership_notin_first_emission >> simp[]])])
QED

Resume ctor_bop_dispatch_first_emission[bytes_eq]:
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_bytestring_hash_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_bytestring_hash_first_emission] >>
  gen_tac >> Cases_on `op = Eq` >> simp[]
  >- (ho_match_mp_tac ctor_as_stack_val_first_emission >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
  irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]
QED

Finalise ctor_bop_dispatch_first_emission

Theorem ctor_guarded_bop_dispatch_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))) ==>
  !env rt ty op args a x b. compile_builtin_dispatch_body
    (expr_child_callback bound compile_expr) env rt ty (Bop op) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >>
  disch_tac >> drule ctor_bop_dispatch_first_emission >>
  disch_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem ctor_concat_cfn_appends:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env es ptr infos off. cs_appends (compile_concat cfn env es ptr infos off)
Proof
  strip_tac >> rpt gen_tac >> irule ctor_ci_mono_appends >>
  simp[ci_mono_compile_concat_cfn]
QED

Theorem ctor_make_array_cfn_appends:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env es ty size lw ptr. cs_appends (compile_make_array cfn env es ty size lw ptr)
Proof
  strip_tac >> rpt gen_tac >> irule ctor_ci_mono_appends >>
  simp[ci_mono_compile_make_array_cfn]
QED

Theorem ctor_make_tuple_cfn_appends:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env es ptr off. cs_appends (compile_make_tuple cfn env es ptr off)
Proof
  strip_tac >> rpt gen_tac >> irule ctor_ci_mono_appends >>
  simp[ci_mono_compile_make_tuple_cfn]
QED

Theorem ctor_concat_dispatch_first_emission:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env rt ty max_len args a x b.
    compile_builtin_dispatch_body cfn env rt ty (Concat max_len) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[ctor_alloc_buffer_appends] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_concat_cfn_appends >> simp[]) >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  simp[cs_appends_def, cs_extends_refl]
QED

Theorem ctor_make_array_dispatch_first_emission:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env rt ty elem_ty_opt bnd args a x b.
    compile_builtin_dispatch_body cfn env rt ty (MakeArray elem_ty_opt bnd) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 6 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `elem_ty_opt` >> simp_tac (srw_ss()) [LET_THM] >>
  (rewrite_tac[state_pair_let_bind] >>
   ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- metis_tac[ctor_alloc_buffer_first_emission] >>
   gen_tac >> rpt gen_tac >> disch_tac >>
   qmatch_asmsub_abbrev_tac `as_ptr_val rt LocMemory res` >>
   Cases_on `res` >> gvs[as_ptr_val_def] >>
   FIRST [(drule ctor_make_tuple_cfn_appends >> simp[cs_appends_def] >>
           disch_then drule >> simp[] >> NO_TAC),
          (drule ctor_make_array_cfn_appends >> simp[cs_appends_def] >>
           disch_then drule >> simp[])])
QED

Theorem ctor_guarded_concat_dispatch_first_emission:
  !bound env rt ty max_len args a x b.
    compile_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env rt ty (Concat max_len) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> disch_tac >> irule ctor_concat_dispatch_first_emission >>
  goal_assum (drule_at Any) >> simp[ctor_expr_callback_ci_mono]
QED

Theorem ctor_guarded_make_array_dispatch_first_emission:
  !bound env rt ty elem_ty_opt bnd args a x b.
    compile_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env rt ty (MakeArray elem_ty_opt bnd) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> disch_tac >> irule ctor_make_array_dispatch_first_emission >>
  goal_assum (drule_at Any) >> simp[ctor_expr_callback_ci_mono]
QED

Theorem ctor_uint2str_first_emission:
  !v digits size a x b. compile_uint2str v digits size a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> rewrite_tac[builtinStringsTheory.compile_uint2str_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac cs_appends_bind >> conj_tac
       >- simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return] >>
       gen_tac) >>
  simp[cs_appends_return]
QED

Theorem ctor_as_wei_value_int_first_emission:
  !v scale signed a x b. compile_as_wei_value_int v scale signed a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> Cases_on `scale = 1`
  >- simp[builtinMiscTheory.compile_as_wei_value_int_def, comp_return_def,
          cs_extends_refl] >>
  `!ok. cs_appends (if signed then
       comp_bind (emit_op SLT [v; Lit 0w]) (\pos.
       comp_bind (emit_op ISZERO [pos]) (\nn. emit_op AND [nn; ok]))
       else return ok)` by
    (gen_tac >> Cases_on `signed` >> simp[cs_appends_return] >>
     ho_match_mp_tac cs_appends_bind >> conj_tac
     >- simp[cs_appends_emit_helpers] >>
     gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
     >- simp[cs_appends_emit_helpers] >> simp[cs_appends_emit_helpers]) >>
  asm_simp_tac (srw_ss()) [builtinMiscTheory.compile_as_wei_value_int_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def, comp_ignore_bind_def] >>
  ntac 4 (ho_match_mp_tac cs_appends_bind >> conj_tac
          >- simp[cs_appends_emit_helpers] >> gen_tac) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> simp[cs_appends_return]
QED

Theorem ctor_as_wei_value_decimal_first_emission:
  !v scale divisor a x b. compile_as_wei_value_decimal v scale divisor a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
       i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> rewrite_tac[builtinMiscTheory.compile_as_wei_value_decimal_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def, comp_ignore_bind_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> Cases_on `scale = 1` >> simp[cs_appends_emit_helpers] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_uint2str_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env rt ty max_len args a x b.
    compile_builtin_dispatch_body cfn env rt ty (Uint2Str max_len) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  rpt gen_tac >> disch_tac >> drule ctor_uint2str_first_emission >> simp[]
QED

Theorem ctor_as_wei_value_dispatch_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env rt ty denom args a x b.
    compile_builtin_dispatch_body cfn env rt ty (AsWeiValue denom) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp_tac (srw_ss()) [Once compile_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> Cases_on `is_decimal_type (expr_type (HD args))` >> simp[] >>
  (ho_match_mp_tac ctor_as_stack_val_first_emission >> rpt gen_tac >> disch_tac >>
   FIRST [drule ctor_as_wei_value_decimal_first_emission,
          drule ctor_as_wei_value_int_first_emission] >> simp[])
QED

Theorem ctor_guarded_uint2str_dispatch_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env rt ty max_len args a x b.
    compile_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env rt ty (Uint2Str max_len) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >>
  disch_tac >> drule ctor_uint2str_dispatch_first_emission >>
  disch_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem ctor_guarded_as_wei_value_dispatch_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env rt ty denom args a x b.
    compile_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env rt ty (AsWeiValue denom) args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >>
  disch_tac >> drule ctor_as_wei_value_dispatch_first_emission >>
  disch_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem ctor_attribute_first_emission:
  (!a x b. cfn env ty base_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_attribute cfn env rt ty base_e fld a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[compile_attribute_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- simp[] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem ctor_attribute_body_first_emission:
  (!a x b. cfn env ty base_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_expr_body cfn bfn tfn env ty (Attribute ann base_e fld) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  ho_match_mp_tac ctor_attribute_first_emission >> simp[]
QED

Theorem ctor_attribute_body_guarded_first_emission:
  (!e env ty a. expr_size e < expr_size (Attribute ann base_e fld) ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_expr_body
    (expr_child_callback (expr_size (Attribute ann base_e fld)) compile_expr)
    bfn tfn env ty (Attribute ann base_e fld) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  ho_match_mp_tac ctor_attribute_body_first_emission >> metis_tac[]
QED

Theorem ctor_subscript_first_emission:
  (!a x b. cfn env ty base_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ity a x b. cfn env ity idx_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_subscript cfn env rt ty base_e idx_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[compile_subscript_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> Cases_on `place_type env base_e`
  >- suspend "map_place"
  >> suspend "value_place"
QED

Resume ctor_subscript_first_emission[map_place]:
  simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC
      >- metis_tac[ctor_keccak256_key_first_emission] >>
      simp[comp_return_def, cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_mapping_subscript_first_emission] >>
  simp[comp_return_def, cs_extends_refl]
QED

Resume ctor_subscript_first_emission[value_place]:
  qpat_x_assum `place_type env base_e = ValPT t` kall_tac >>
  Cases_on `t` >> simp_tac (srw_ss()) [LET_THM] >>
  (ho_match_mp_tac first_emission_bind >> conj_tac
   >- FIRST [(ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]),
             metis_tac[ctor_tuple_subscript_first_emission]] >>
   gen_tac >> FIRST [simp[comp_return_def, cs_extends_refl] >> NO_TAC,
     (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >>
          rpt gen_tac >> disch_tac >>
          drule_at Any ctor_array_subscript_first_emission >>
          (impl_tac >- metis_tac[ctor_ptr_load_first_emission]) >> simp[]) >>
      simp[comp_return_def, cs_extends_refl])])
QED

Finalise ctor_subscript_first_emission

Theorem ctor_subscript_body_first_emission:
  (!a x b. cfn env ty base_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ity a x b. cfn env ity idx_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_expr_body cfn bfn tfn env ty (Subscript ann base_e idx_e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  ho_match_mp_tac ctor_subscript_first_emission >> metis_tac[]
QED

Theorem ctor_subscript_body_guarded_first_emission:
  (!e env ty a. expr_size e < expr_size (Subscript ann base_e idx_e) ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_expr_body
    (expr_child_callback (expr_size (Subscript ann base_e idx_e)) compile_expr)
    bfn tfn env ty (Subscript ann base_e idx_e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  ho_match_mp_tac ctor_subscript_body_first_emission >> metis_tac[]
QED

Theorem ctor_struct_lit_cfn_appends:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env ty flds ptr off. cs_appends (compile_struct_lit cfn env ty flds ptr off)
Proof
  strip_tac >> rpt gen_tac >> irule ctor_ci_mono_appends >>
  simp[ci_mono_compile_struct_lit_cfn]
QED

Theorem ctor_structlit_body_first_emission:
  (!env ty e a. ci_mono a (SND (cfn env ty e a))) ==>
  !env ty ann nm flds a x b.
    compile_expr_body cfn bfn tfn env ty (StructLit ann nm flds) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_struct_lit_cfn_appends >> simp[]) >>
  simp[cs_appends_def, cs_extends_refl]
QED

Theorem ctor_structlit_body_guarded_first_emission:
  !env ty ann nm flds a x b.
    compile_expr_body
      (expr_child_callback (expr_size (StructLit ann nm flds)) compile_expr)
      bfn tfn env ty (StructLit ann nm flds) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> disch_tac >> irule ctor_structlit_body_first_emission >>
  goal_assum (drule_at Any) >> simp[ctor_expr_callback_ci_mono]
QED

Theorem ctor_addmod_names_body_first_emission:
  !env ty ann aty an bty bn mty mn a x b.
    compile_expr_body cfn bfn tfn env ty
      (Builtin ann AddMod [Name aty an; Name bty bn; Name mty mn]) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 9 gen_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, compile_addmod_names_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >> BETA_TAC >>
  rpt (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[ctor_name_vv_first_emission,
                 ctor_unwrap_value_first_emission] >> gen_tac) >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >>
  metis_tac[ctor_addmod_first_emission_strong]
QED

Theorem ctor_mulmod_names_body_first_emission:
  !env ty ann aty an bty bn mty mn a x b.
    compile_expr_body cfn bfn tfn env ty
      (Builtin ann MulMod [Name aty an; Name bty bn; Name mty mn]) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 9 gen_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, compile_mulmod_names_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >> BETA_TAC >>
  rpt (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[ctor_name_vv_first_emission,
                 ctor_unwrap_value_first_emission] >> gen_tac) >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >>
  metis_tac[ctor_mulmod_first_emission_strong]
QED

Theorem ctor_powmod256_names_body_first_emission:
  !env ty ann aty an bty bn a x b.
    compile_expr_body cfn bfn tfn env ty
      (Builtin ann PowMod256 [Name aty an; Name bty bn]) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 7 gen_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, compile_powmod256_names_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >> BETA_TAC >>
  rpt (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[ctor_name_vv_first_emission,
                 ctor_unwrap_value_first_emission] >> gen_tac) >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  ho_match_mp_tac first_emission_strong >>
  metis_tac[ctor_pow_mod256_first_emission_strong]
QED

Theorem ctor_name_target_first_emission:
  !env id a x b. compile_get_target_ptr cfn env (NameTarget id) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `FLOOKUP env.ce_vars id` >>
  simp[compile_get_target_ptr_def, comp_return_def, cs_extends_refl] >>
  rename1 `FLOOKUP env.ce_vars id = SOME vloc` >> Cases_on `vloc` >>
  simp[compile_get_target_ptr_def, comp_return_def, cs_extends_refl]
QED

Theorem ctor_top_level_name_target_first_emission:
  !env nsid a x b. compile_get_target_ptr cfn env (TopLevelNameTarget nsid) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `FLOOKUP env.ce_module_vars nsid` >>
  simp[compile_get_target_ptr_def, comp_return_def, cs_extends_refl] >>
  rename1 `FLOOKUP env.ce_module_vars nsid = SOME vloc` >> Cases_on `vloc` >>
  simp[compile_get_target_ptr_def, comp_return_def, cs_extends_refl]
QED

Theorem ctor_attribute_target_first_emission:
  (!a x b. compile_get_target_ptr cfn env bt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_get_target_ptr cfn env (AttributeTarget bt fld) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[Once compile_get_target_ptr_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac >- simp[] >>
  gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem ctor_pop_body_first_emission:
  (!a x b. compile_get_target_ptr cfn env target a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_expr_body cfn bfn tfn env ty (Pop ann target) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac >- simp[] >>
  gen_tac >> PairCases_on `x` >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_dynarray_pop_first_emission] >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem ctor_subscript_target_first_emission:
  (!a x b. compile_get_target_ptr cfn env bt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!a x b. cfn env (expr_type idx_e) idx_e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_get_target_ptr cfn env (SubscriptTarget bt idx_e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[Once compile_get_target_ptr_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac >- simp[] >>
  qx_gen_tac `result` >> PairCases_on `result` >> simp_tac (srw_ss()) [LET_THM] >>
  namedCases_on `result2` ["", "pt"] >> simp_tac (srw_ss()) [LET_THM]
  >- suspend "array_target" >>
  Cases_on `pt` >> simp_tac (srw_ss()) [LET_THM]
  >- suspend "map_target"
  >> suspend "value_target"
QED

Resume ctor_subscript_target_first_emission[array_target]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule_at Any ctor_array_subscript_first_emission >>
      (impl_tac >- metis_tac[ctor_ptr_load_first_emission]) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Resume ctor_subscript_target_first_emission[value_target]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> disch_tac >>
      drule_at Any ctor_array_subscript_first_emission >>
      (impl_tac >- metis_tac[ctor_ptr_load_first_emission]) >> simp[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Resume ctor_subscript_target_first_emission[map_target]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >- metis_tac[ctor_keccak256_key_first_emission] >>
      simp[comp_return_def, cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_mapping_subscript_first_emission] >>
  simp[comp_return_def, cs_extends_refl]
QED

Finalise ctor_subscript_target_first_emission

Theorem ctor_maxvalue_type_dispatch_first_emission:
  !env vt ty rt args a x b.
    compile_type_builtin_dispatch_body cfn env vt ty MaxValue rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> Cases_on `type_bounds rt` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM, cs_extends_refl]
QED

Theorem ctor_minvalue_type_dispatch_first_emission:
  !env vt ty rt args a x b.
    compile_type_builtin_dispatch_body cfn env vt ty MinValue rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> Cases_on `type_bounds rt` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM, cs_extends_refl]
QED

Theorem ctor_epsilon_type_dispatch_first_emission:
  !env vt ty rt args a x b.
    compile_type_builtin_dispatch_body cfn env vt ty Epsilon rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp[compile_type_builtin_dispatch_body_def, cs_extends_refl]
QED

Theorem ctor_empty_type_dispatch_first_emission:
  !env vt ty rt args a x b.
    compile_type_builtin_dispatch_body cfn env vt ty Empty rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> Cases_on `is_word_type rt` >>
  simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_body_def, LET_THM]
  >- simp[cs_extends_refl] >>
  simp[] >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[ctor_builtin_empty_complex_first_emission_strong]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem ctor_extract32_type_dispatch_first_emission:
  (!a x b. cfn env (expr_type (HD args)) (HD args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!a x b. cfn env ty (EL 1 args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn env vt ty Extract32 rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[ctor_bytestring_src_first_emission_strong]) >>
  qx_gen_tac `src` >> PairCases_on `src` >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[ctor_extract32_load_first_emission_strong]) >>
  gen_tac >> ho_match_mp_tac ctor_as_stack_val_first_emission >>
  metis_tac[ctor_clamp_basetype_first_emission]
QED

Theorem ctor_copy_memory_appends:
  !dst src n. cs_appends (compile_copy_memory dst src n)
Proof
  ntac 2 gen_tac >> Cases >>
  simp[compile_copy_memory_def, cs_appends_return, cs_appends_emit_helpers]
QED

Theorem ctor_bytestring_widen_copy_first_emission:
  !dst v src a x b. compile_bytestring_widen_copy dst v src a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_bytestring_widen_copy_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >>
  simp[ctor_copy_memory_appends, cs_appends_return]
QED

Theorem ctor_convert_type_dispatch_first_emission:
  (!a x b. cfn env (expr_type (HD args)) (HD args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn env vt ty Convert rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ is_word_type rt /\
    (lowered_value_type env (HD args) = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type env (HD args) = BaseT (StringT 0))`
  >- simp[cs_extends_refl] >>
  simp[] >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ is_bytestring_type rt /\
    type_memory_bytes env (lowered_value_type env (HD args)) < type_memory_bytes env rt` >>
  simp[]
  >- (ho_match_mp_tac ctor_as_stack_val_first_emission >>
      metis_tac[ctor_bytestring_widen_copy_first_emission]) >>
  Cases_on `rt` >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac ctor_as_stack_val_first_emission >>
  metis_tac[ctor_type_convert_first_emission]
QED

Theorem ctor_lower_abi_decode_first_emission_strong:
  !data info amin amax size a x b.
    lower_abi_decode data info amin amax size a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 5 gen_tac >> rewrite_tac[lower_abi_decode_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >>
      rpt (ho_match_mp_tac cs_appends_bind >> conj_tac
           >- simp[cs_appends_emit_helpers] >> gen_tac) >>
      simp[cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_alloc_buffer]) >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_return] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[CONJUNCT1 ci_mono_compile_abi_decode]) >>
  simp[cs_appends_return]
QED

Theorem ctor_abi_decode_type_dispatch_first_emission:
  (!a x b. cfn env (expr_type (HD args)) (HD args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn env vt ty (AbiDecode unwrap) rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_body_def, LET_THM] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
  ho_match_mp_tac first_emission_strong >>
  metis_tac[ctor_lower_abi_decode_first_emission_strong]
QED

Theorem ctor_compile_store_abi_tuple_appends:
  !env buf off elems. cs_appends (compile_store_abi_tuple env buf off elems)
Proof
  ntac 2 gen_tac >> Induct_on `elems`
  >- simp[compile_store_abi_tuple_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> gen_tac >> rewrite_tac[compile_store_abi_tuple_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_emit_helpers, ctor_copy_memory_appends]) >>
  simp[]
QED

Theorem ctor_lower_abi_encode_first_emission_strong:
  !ensure mid src info maxlen a x b.
    lower_abi_encode ensure mid src info maxlen a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 5 gen_tac >> simp_tac (srw_ss()) [lower_abi_encode_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_return] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (Cases_on `mid` >> simp[cs_appends_return] >>
      ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[cj 2 ci_mono_compile_abi_encode]) >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_emit_helpers] >>
      ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  simp[cs_appends_return]
QED

Theorem ctor_materialize_vv_first_emission:
  !env ty vv a x b. compile_materialize_vv env ty vv a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_materialize_vv_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_unwrap_value]) >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_store_memory]) >>
  simp[cs_appends_return]
QED

Theorem ctor_abi_encode_args_first_emission:
  !es. (!e. MEM e es ==> !a x b. cfn env (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_abi_encode_args cfn env es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct
  >- (simp[compile_abi_encode_args_def, comp_return_def] >> rpt strip_tac >>
      gvs[cs_extends_refl]) >>
  gen_tac >> strip_tac >> simp_tac (srw_ss()) [Once compile_abi_encode_args_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[listTheory.MEM] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC
      >- metis_tac[ctor_materialize_vv_first_emission] >>
      metis_tac[ctor_unwrap_value_first_emission]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum ho_match_mp_tac >> metis_tac[listTheory.MEM]) >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_abi_encode_type_dispatch_first_emission:
  (!e. MEM e args ==> !a x b. cfn env (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_type_builtin_dispatch_body cfn env vt ty (AbiEncode ensure mid) rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `LENGTH args = 1 /\ ~ensure` >> simp[]
  >- (`MEM (HD args) args` by (Cases_on `args` >> gvs[]) >>
      Cases_on `is_word_type (expr_type (HD args))` >> simp[] >>
      rewrite_tac[state_pair_let_bind]
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_alloc_buffer_first_emission]) >>
          gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
              irule (cj 2 first_emission_emit_helpers) >> goal_assum $ drule_at Any >> simp[]) >>
          gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
          ho_match_mp_tac first_emission_strong >> metis_tac[ctor_lower_abi_encode_first_emission_strong]) >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[] >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_unwrap_value_first_emission] >>
      gen_tac >> ho_match_mp_tac ctor_as_ptr_val_first_emission >>
      ho_match_mp_tac first_emission_strong >> metis_tac[ctor_lower_abi_encode_first_emission_strong]) >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_abi_encode_args_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[ctor_compile_store_abi_tuple_appends] >>
  gen_tac >> rewrite_tac[cs_appends_def] >>
  rpt gen_tac >> BETA_TAC >> qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory encoded_result` >>
  Cases_on `encoded_result` >> simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  drule ctor_lower_abi_encode_first_emission_strong >> simp[]
QED

Theorem ctor_guarded_abi_encode_type_dispatch_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env vt ty ensure mid rt args a x b.
    compile_type_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env vt ty (AbiEncode ensure mid) rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  rpt gen_tac >> disch_tac >> irule ctor_abi_encode_type_dispatch_first_emission >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem ctor_invalid_stack_first_emission_strong[local]:
  !rt a x b.
    (let (_,s) = emit_inst INVALID [] [] a in (StackValue rt (Lit 0w),s)) = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> Cases_on `emit_inst INVALID [] [] a` >> simp[] >> strip_tac >> gvs[] >>
  irule (cj 1 first_emission_emit_helpers) >> goal_assum $ drule_at Any >> simp[]
QED

Theorem ctor_invalid_call_first_emission_strong:
  !target. (target = SelfDestructTarget) ==>
  !env rt ty args def a x b. compile_call cfn env rt ty target args def a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> strip_tac >> gvs[] >>
  simp_tac (srw_ss()) [compile_call_def] >>
  metis_tac[ctor_invalid_stack_first_emission_strong]
QED

Theorem ctor_raw_revert_first_emission[local]:
  !data a x b. builtinSystem$compile_raw_revert data a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[builtinSystemTheory.compile_raw_revert_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
  gen_tac >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_real_system_call_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !target. (target = RawLog \/ target = RawRevert) ==>
  !env rt ty args def a x b. compile_call cfn env rt ty target args def a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> drule ctor_multi_exprs_first_emission >> disch_tac >>
  gen_tac >> strip_tac >> gvs[]
  >- (ntac 3 gen_tac >> namedCases_on `args` ["", "topics rest"] >>
      simp_tac (srw_ss()) [compile_call_def]
      >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
      namedCases_on `rest` ["", "data tail"] >> simp_tac (srw_ss()) []
      >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
      Cases_on `tail` >> simp_tac (srw_ss()) []
      >- (simp_tac (srw_ss()) [LET_THM] >> rewrite_tac[state_pair_let_bind] >>
          ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[] >>
          gen_tac >> Cases_on `expr_type data = BaseT (BytesT (Fixed 32))` >> simp[]
          >- (ho_match_mp_tac first_emission_bind >> conj_tac
              >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_alloc_buffer_first_emission]) >>
              gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
              >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
              gen_tac >> ho_match_mp_tac first_emission_strong >>
              ho_match_mp_tac first_emission_strong_bind >> conj_tac
              >- (rpt gen_tac >> strip_tac >> irule (cj 2 first_emission_emit_helpers) >>
                  goal_assum $ drule_at Any >> simp[]) >>
              gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
              ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
              simp[cs_appends_def, cs_extends_refl]) >>
          ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac first_emission_strong >>
          ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
              goal_assum $ drule_at Any >> simp[]) >>
          gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
          ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
          gen_tac >> simp_tac (srw_ss()) [SF ETA_ss] >>
          ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
          simp[cs_appends_def, cs_extends_refl]) >>
      ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  ntac 3 gen_tac >> namedCases_on `args` ["", "data tail"] >>
  simp_tac (srw_ss()) [compile_call_def]
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  Cases_on `tail` >> simp_tac (srw_ss()) []
  >- (simp_tac (srw_ss()) [LET_THM] >> rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[ctor_raw_revert_first_emission] >>
      simp[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]
QED

Theorem ctor_send_call_first_emission:
  (!e. MEM e args ==> !ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt ty has_gas def a x b. compile_call cfn env rt ty (Send has_gas) args def a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 4 gen_tac >> namedCases_on `args` ["", "addr_e rest"] >>
  simp_tac (srw_ss()) [compile_call_def]
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  namedCases_on `rest` ["", "val_e gas_es"] >> simp_tac (srw_ss()) []
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  Cases_on `LENGTH gas_es = (if has_gas then 1 else 0)` >> simp[]
  >- (rewrite_tac[state_pair_let_bind] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
      gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (namedCases_on `gas_es` ["", "gas_e tail"]
          >- simp[cs_extends_refl] >>
          Cases_on `tail` >> simp[]
          >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
          simp[cs_extends_refl]) >>
      gen_tac >> ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
          goal_assum $ drule_at Any >> simp[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers, cs_appends_return] >>
      simp[cs_appends_def, cs_extends_refl]) >>
  ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]
QED

Theorem ctor_guarded_send_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann has_gas args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann (Send has_gas) args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_send_call_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_guarded_real_system_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !target. (target = RawLog \/ target = RawRevert) ==>
  !env ty ann args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann target args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_real_system_call_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_invalid_call_expr_first_emission_strong:
  !target. (target = SelfDestructTarget) ==>
  !env ty ann args def a x b.
    compile_expr_body cfn bfn tfn env ty (Call ann target args def) a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> disch_tac >> simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_invalid_call_first_emission_strong >> simp[]
QED

Theorem ctor_stage_intcall_args_first_emission:
  !env vals flags tys a x b.
    compile_stage_intcall_args env vals flags tys a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- (simp[Once compile_stage_intcall_args_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl])
  >- (rpt gen_tac >> strip_tac >>
      simp_tac (srw_ss()) [Once compile_stage_intcall_args_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_unwrap_value_first_emission] >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[] >>
      simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl])
  >- (rpt gen_tac >> strip_tac >>
      simp_tac (srw_ss()) [Once compile_stage_intcall_args_def, LET_THM] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_unwrap_value_first_emission] >>
      gen_tac >> ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[ctor_alloc_buffer_first_emission] >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >> simp[cs_appends_emit_helpers] >>
          IF_CASES_TAC
          >- (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
              >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_store_bytestring]) >>
              simp[cs_appends_return]) >>
          irule ctor_ci_mono_appends >> simp[ci_mono_compile_store_memory]) >>
      ho_match_mp_tac cs_appends_bind >> conj_tac
      >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_stage_intcall_args]) >>
      simp[cs_appends_return]) >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[Once compile_stage_intcall_args_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  gen_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [comp_bind_def, comp_return_def] >>
  Cases_on `compile_stage_intcall_args env vals [] [] b` >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[ctor_unwrap_value_first_emission]
QED

Theorem ctor_multi_vvs_members_first_emission:
  !es. (!e. MEM e es ==> !a x b. cfn env (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_multi_vvs cfn env es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct
  >- (simp[compile_multi_vvs_def, comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  gen_tac >> strip_tac >> rewrite_tac[Once compile_multi_vvs_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[listTheory.MEM] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum ho_match_mp_tac >> metis_tac[listTheory.MEM]) >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_fresh_vars_first_emission[local]:
  !n a x b. fresh_vars n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >> rewrite_tac[emitHelperTheory.fresh_vars_def]
  >- (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (simp[fresh_var_def] >> rpt strip_tac >> gvs[] >>
      irule cs_extends_same_block >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[] >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_emit_multi_op_first_emission[local]:
  !opc ops n. opc <> PHI ==> !a x b. emit_multi_op opc ops n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[emitHelperTheory.emit_multi_op_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_fresh_vars_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 1 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_store_multi_results_first_emission[local]:
  !buf ops offset a x b. store_multi_results buf ops offset a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> Cases >> gen_tac >> rewrite_tac[Once store_multi_results_def]
  >- (simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  irule ctor_ci_mono_appends >> simp[ci_mono_store_multi_results]
QED

Theorem ctor_int_call_first_emission:
  (!e. MEM e args ==> !ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt ty func_id def a x b. compile_call cfn env rt ty (IntCall func_id) args def a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_multi_vvs_members_first_emission >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `returns_count > 0` >> simp[]
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_alloc_buffer_first_emission]) >>
          simp[cs_extends_refl]) >>
      Cases_on `return_buf_size > 0` >> simp[cs_extends_refl] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_alloc_buffer_first_emission]) >>
      simp[cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_stage_intcall_args_first_emission] >>
  gen_tac >> Cases_on `returns_count > 0` >> simp[]
  >- (Cases_on `return_buf` >> simp[]
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
              irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
          simp[cs_extends_refl]) >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_at (Pos last) ctor_emit_multi_op_first_emission >> simp[]) >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_store_multi_results_first_emission] >>
      simp[cs_extends_refl]) >>
  Cases_on `return_buf` >> simp[] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 2 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  simp[cs_extends_refl] >> rpt gen_tac >> strip_tac >>
  qspec_then `INVOKE` mp_tac (cj 2 first_emission_emit_helpers) >>
  simp[] >> disch_then drule >> metis_tac[]
QED

Theorem ctor_guarded_int_call_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann func_id args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann (IntCall func_id) args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_int_call_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_ext_call_kwarg_first_emission:
  (!ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt k a x b. compile_ext_call_kwarg cfn env rt k e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 2 gen_tac >>
  rewrite_tac[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (simp_tac (srw_ss()) [LET_THM] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[] >>
      gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_materialize_vv_first_emission]) >>
      simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >>
  gen_tac >> simp[comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_ext_call_kwargs_first_emission:
  !ks es. (!e. MEM e es ==> !ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt a x b. compile_ext_call_kwargs cfn env rt ks es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct
  >- (simp[compile_ext_call_kwargs_def, comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  gen_tac >> Cases
  >- (simp[compile_ext_call_kwargs_def, comp_return_def] >> rpt strip_tac >> gvs[cs_extends_refl]) >>
  strip_tac >> gen_tac >> rewrite_tac[Once compile_ext_call_kwargs_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      drule_at (Pos last) ctor_ext_call_kwarg_first_emission >>
      disch_then irule >> metis_tac[listTheory.MEM]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (qpat_x_assum `!es. _` (qspec_then `t` mp_tac) >>
      impl_tac >- metis_tac[listTheory.MEM] >>
      disch_then (qspec_then `rt` ACCEPT_TAC)) >>
  gen_tac >> PairCases_on `x` >> simp[comp_return_def] >>
  rpt strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_raw_call_outbuf_first_emission:
  !n a x b. compile_raw_call_outbuf n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[builtinSystemTheory.compile_raw_call_outbuf_def] >>
  IF_CASES_TAC >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission]
  >- (gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_bind >> simp[cs_appends_return] >>
      gen_tac >> ho_match_mp_tac cs_appends_bind >>
      simp[cs_appends_emit_helpers, cs_appends_return])
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_return]
QED

Theorem ctor_raw_call_calldata_first_emission:
  (!e. MEM e args ==> !ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt ty rcf def a x b. compile_call cfn env rt ty (RawCallCalldataTarget rcf) args def a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 4 gen_tac >> namedCases_on `args` ["", "addr_e kw_es"] >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt gen_tac >> disch_tac >> drule_at (Pos last) ctor_ext_call_kwargs_first_emission >>
      disch_then irule >> metis_tac[listTheory.MEM]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `x1` >> simp[cs_extends_refl] >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_raw_call_outbuf_first_emission] >>
  gen_tac >> PairCases_on `x` >> simp[] >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_msg_data_to_memory]) >>
  qx_gen_tac `dp` >> PairCases_on `dp` >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_raw_call_finish]) >>
  gen_tac >> rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >>
  rewrite_tac[cs_appends_def] >> simp[cs_extends_refl] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_raw_call_first_emission:
  (!e. MEM e args ==> !ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt ty rcf def a x b. compile_call cfn env rt ty (RawCallTarget rcf) args def a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 4 gen_tac >> namedCases_on `args` ["", "addr_e rest"] >>
  simp_tac (srw_ss()) [compile_call_def]
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  namedCases_on `rest` ["", "data_e kw_es"] >> simp_tac (srw_ss()) [LET_THM]
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt gen_tac >> disch_tac >> drule_at (Pos last) ctor_ext_call_kwargs_first_emission >>
      disch_then irule >> metis_tac[listTheory.MEM]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `x1` >> simp[cs_extends_refl] >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_raw_call_outbuf_first_emission] >>
  gen_tac >> PairCases_on `x` >> simp[] >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_raw_call_finish]) >>
  gen_tac >> rewrite_tac[cs_appends_def] >> rpt gen_tac >> BETA_TAC >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_guarded_raw_call_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann rcf args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann (RawCallTarget rcf) args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_raw_call_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_guarded_raw_call_calldata_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann rcf args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann (RawCallCalldataTarget rcf) args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_raw_call_calldata_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_extcall_store_values_ci_mono[local]:
  !vals env buf off a.
    ci_mono a (SND (compile_extcall_store_values env vals buf off a))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_extcall_store_values_def, ci_mono_comp_return] >>
  PairCases_on `h` >> simp[Once compile_extcall_store_values_def, LET_THM] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_unwrap_value] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_emit_void, ci_mono_compile_store_bytestring] >>
      IF_CASES_TAC >> simp[ci_mono_emit_void, ci_mono_compile_store_bytestring]) >>
  rpt strip_tac >> first_x_assum irule
QED

Theorem ctor_extcodesize_check_ci_mono[local]:
  !op a. ci_mono a (SND (compile_extcodesize_check op a))
Proof
  rpt gen_tac >> simp[compile_extcodesize_check_def] >> BETA_TAC >>
  irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ctor_external_call_kwargs_first_emission:
  !env addr vals tys memsz abisz mid retsz minsz retmem static value gas skip hasdef def rt dt enc dec.
  !a x b. compile_external_call_kwargs env addr vals tys memsz abisz mid retsz minsz
    retmem static value gas skip hasdef def rt dt enc dec a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 20 gen_tac >> simp_tac (srw_ss()) [compile_external_call_kwargs_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  rewrite_tac[GSYM cs_appends_def] >> irule ctor_ci_mono_appends >>
  gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_emit_void] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >- simp[ci_mono_comp_return] >>
      ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
      rpt gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ctor_extcall_store_values_ci_mono] >>
      rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
      rpt gen_tac >> ho_match_mp_tac ci_mono_bind >>
      simp[cj 2 ci_mono_compile_abi_encode, ci_mono_emit_op]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >> simp[ctor_extcodesize_check_ci_mono, ci_mono_comp_return]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >> simp[ci_mono_emit_op]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
  rpt gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >>
      simp[ci_mono_emit_void, ci_mono_emit_inst]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >>
  rpt gen_tac >> IF_CASES_TAC >- simp[ci_mono_comp_return] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
      rpt gen_tac >> simp[ci_mono_compile_default_return_path]) >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
  rpt gen_tac >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_return_value_decode] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >>
  simp[ci_mono_compile_abi_decode, ci_mono_comp_return]
QED

Theorem ctor_ext_call_first_emission:
  (!e. MEM e args ==> !ety a x b. cfn env ety e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !rt ty static skip name tys ret opts def a x b.
    compile_call cfn env rt ty (ExtCall static skip (name,tys,ret) opts) args def a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 9 gen_tac >> namedCases_on `args` ["", "addr_e rest"] >>
  simp_tac (srw_ss()) [compile_call_def, LET_THM]
  >- (ho_match_mp_tac first_emission_strong >> metis_tac[ctor_invalid_stack_first_emission_strong]) >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac ctor_multi_vvs_members_first_emission >>
      metis_tac[listTheory.MEM, rich_listTheory.MEM_TAKE]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt gen_tac >> disch_tac >> drule_at (Pos last) ctor_ext_call_kwargs_first_emission >>
      disch_then irule >> metis_tac[listTheory.MEM, rich_listTheory.MEM_DROP_IMP]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  Cases_on `x2` >> simp[]
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (Cases_on `x1` >> simp[cs_extends_refl] >>
          ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
      gen_tac >> ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[ctor_external_call_kwargs_first_emission] >>
      gen_tac >> rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[cs_extends_refl]) >>
  PairCases_on `x` >> simp[] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (Cases_on `x1` >> simp[cs_extends_refl] >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_external_call_kwargs_first_emission] >>
  gen_tac >> rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[cs_extends_refl]
QED

Theorem ctor_guarded_ext_call_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann static skip name tys ret opts args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann (ExtCall static skip (name,tys,ret) opts) args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >>
  rpt gen_tac >> disch_tac >>
  drule_at (Pos last) ctor_ext_call_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_check_create_result_ci_mono[local]:
  !addr rof a. ci_mono a (SND (compile_check_create_result addr rof a))
Proof
  rpt gen_tac >> Cases_on `rof` >> simp[compile_check_create_result_def] >>
  rpt (FIRST [
    ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label, ci_mono_emit_op, ci_mono_compile_alloc_buffer],
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst, ci_mono_new_block, ci_mono_emit_void],
    gen_tac]) >> simp[ci_mono_comp_return]
QED

Theorem ctor_create_dispatch_ci_mono[local]:
  !ptr len value salt rof a.
    ci_mono a (SND (compile_create_dispatch ptr len value salt rof a))
Proof
  rpt gen_tac >> simp[compile_create_dispatch_def] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (Cases_on `salt` >> simp[ci_mono_emit_op]) >>
  simp[ctor_check_create_result_ci_mono]
QED

Theorem ctor_create_copy_ci_mono[local]:
  !target value salt rof a.
    ci_mono a (SND (compile_create_copy target value salt rof a))
Proof
  rpt gen_tac >> Cases_on `salt` >> Cases_on `rof` >>
  simp[compile_create_copy_def, compile_alloc_dynamic_def] >>
  rpt (FIRST [
    ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op],
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void, ci_mono_comp_return],
    gen_tac]) >> simp[ctor_check_create_result_ci_mono]
QED

Theorem ctor_create_blueprint_append_ci_mono[local]:
  !target value salt offset size ptr len rof a.
    ci_mono a (SND (compile_create_blueprint_append target value salt offset size ptr len rof a))
Proof
  rpt gen_tac >> Cases_on `salt` >> Cases_on `rof` >> Cases_on `len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, compile_alloc_dynamic_def] >>
  rpt (FIRST [
    gen_tac,
    CHANGED_TAC (simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                     ctor_check_create_result_ci_mono, ci_mono_compile_copy_memory_dynamic]),
    ho_match_mp_tac ci_mono_bind >> conj_tac,
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac])
QED

Theorem ctor_create_proxy_buf_first_emission_strong:
  !target a x b. compile_create_proxy_buf target a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  gen_tac >> rewrite_tac[compile_create_proxy_buf_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [gen_tac,
    CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return]),
    ho_match_mp_tac cs_appends_bind >> conj_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac])
QED

Theorem ctor_create_blueprint_check_first_emission_strong:
  !target offset a x b. compile_create_blueprint_check target offset a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_create_blueprint_check_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >>
  rpt (FIRST [gen_tac,
    CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return]),
    ho_match_mp_tac cs_appends_bind >> conj_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac])
QED

Theorem ctor_create_copy_first_emission_strong:
  !target value salt rof a x b. compile_create_copy target value salt rof a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 4 gen_tac >>
  simp_tac (srw_ss()) [compile_create_copy_def, compile_alloc_dynamic_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >> irule ctor_ci_mono_appends >>
  Cases_on `salt` >> Cases_on `rof` >> simp[] >>
  rpt (FIRST [gen_tac,
    CHANGED_TAC (simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                     ctor_check_create_result_ci_mono]),
    ho_match_mp_tac ci_mono_bind >> conj_tac,
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac])
QED

Theorem ctor_create_snapshot_first_emission_strong:
  !env vv ty a x b. compile_create_snapshot env vv ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i.
      lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  ntac 3 gen_tac >> simp_tac (srw_ss()) [compile_create_snapshot_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >> irule ctor_ci_mono_appends >>
  Cases_on `vv_location vv` >> simp[]
  >- (rpt (FIRST [gen_tac,
        CHANGED_TAC (simp[ci_mono_emit_op, ci_mono_comp_return, ci_mono_compile_copy_memory_dynamic]),
        ho_match_mp_tac ci_mono_bind >> conj_tac,
        ho_match_mp_tac ci_mono_ignore_bind >> conj_tac])) >>
  Cases_on `x` >> simp[] >>
  rpt (FIRST [gen_tac,
    CHANGED_TAC (simp[ci_mono_emit_op, ci_mono_comp_return, ci_mono_compile_copy_memory_dynamic,
                     compile_slot_to_memory_def, ci_mono_compile_word_copy_loop, ci_mono_compile_imm_copy_to_memory]),
    ho_match_mp_tac ci_mono_bind >> conj_tac,
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac])
QED

Theorem ctor_create_salt_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env salt a x b. compile_create_salt cfn env salt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 2 gen_tac >> Cases_on `salt` >> simp[compile_create_salt_def]
  >- simp[comp_return_def, cs_extends_refl] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_lower_value_first_emission >>
      disch_then irule >> metis_tac[]) >>
  simp[comp_return_def, cs_extends_refl]
QED

Theorem ctor_raw_create_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce ty e st. ci_mono st (SND (cfn ce ty e st))) ==>
  !env bytecode value args salt rof a x b.
    compile_raw_create cfn env bytecode value args salt rof a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> ntac 6 gen_tac >>
  simp_tac (srw_ss()) [compile_raw_create_def, LET_THM] >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- metis_tac[] >> gen_tac >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_create_snapshot_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >> irule ctor_ci_mono_appends >>
  rpt (FIRST [gen_tac,
    CHANGED_TAC (simp[ci_mono_lower_value_cfn, ci_mono_emit_op, ci_mono_comp_return,
      ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory_dynamic,
      ci_mono_compile_create_ctor_tuple, ci_mono_compile_create_salt,
      ctor_create_dispatch_ci_mono, cj 2 ci_mono_compile_abi_encode]),
    ho_match_mp_tac ci_mono_bind >> conj_tac,
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac,
    IF_CASES_TAC, pairarg_tac])
QED

Theorem ctor_create_call_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce ty e st. ci_mono st (SND (cfn ce ty e st))) ==>
  !env ck salt rof args a x b. compile_create_call cfn env ck salt rof args a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> ntac 5 gen_tac >>
  Cases_on `args` >> simp[compile_create_call_def]
  >- (rewrite_tac[comp_ignore_bind_def] >> ho_match_mp_tac first_emission_strong_bind >>
      conj_tac >- (rpt gen_tac >> strip_tac >> irule (cj 1 first_emission_emit_helpers) >> goal_assum $ drule_at Any >> simp[]) >> simp[comp_return_def, cs_extends_refl]) >>
  Cases_on `t` >> simp[]
  >- (rewrite_tac[comp_ignore_bind_def] >> ho_match_mp_tac first_emission_strong_bind >>
      conj_tac >- (rpt gen_tac >> strip_tac >> irule (cj 1 first_emission_emit_helpers) >> goal_assum $ drule_at Any >> simp[]) >> simp[comp_return_def, cs_extends_refl]) >>
  IF_CASES_TAC
  >- (rewrite_tac[comp_ignore_bind_def] >> ho_match_mp_tac first_emission_strong_bind >>
      conj_tac >- (rpt gen_tac >> strip_tac >> irule (cj 1 first_emission_emit_helpers) >> goal_assum $ drule_at Any >> simp[]) >> simp[comp_return_def, cs_extends_refl]) >>
  Cases_on `ck` >> simp[]
  >- suspend "proxy"
  >- suspend "copy"
  >- suspend "blueprint" >>
  rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_raw_create_first_emission >>
  (impl_tac >- metis_tac[]) >> metis_tac[]
QED

Resume ctor_create_call_first_emission[proxy]:
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_create_proxy_buf_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >> irule ctor_ci_mono_appends >>
  gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_create_salt] >> simp[ctor_create_dispatch_ci_mono]
QED

Resume ctor_create_call_first_emission[copy]:
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_create_salt_first_emission >> disch_then irule >> metis_tac[]) >>
  metis_tac[ctor_create_copy_first_emission_strong]
QED

Resume ctor_create_call_first_emission[blueprint]:
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_create_salt_first_emission >> disch_then irule >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac ctor_first_emission_weak_strong_bind >> conj_tac
  >- (ho_match_mp_tac ctor_lower_value_first_emission >> metis_tac[]) >> gen_tac >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_create_blueprint_check_first_emission_strong] >>
  rewrite_tac[GSYM cs_appends_def] >> gen_tac >> irule ctor_ci_mono_appends >>
  gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_create_blueprint_args] >>
  gen_tac >> pairarg_tac >> simp[ctor_create_blueprint_append_ci_mono]
QED

Finalise ctor_create_call_first_emission

Theorem ctor_guarded_create_call_expr_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann ck salt rof opts args def a x b.
    compile_expr_body (expr_child_callback bound compile_expr) bfn tfn
      env ty (Call ann (CreateTarget ck salt rof opts) args def) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  simp_tac (srw_ss()) [Once compile_expr_body_def, compile_call_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `compile_create_call (expr_child_callback bound compile_expr) env ck salt rof args a` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[] >>
  drule_at (Pos last) ctor_create_call_first_emission >>
  (impl_tac >- (conj_tac >- (simp[exprCallBoundsTheory.expr_child_callback_def] >> metis_tac[]) >> simp[ctor_expr_callback_ci_mono])) >> metis_tac[]
QED

Theorem ctor_guarded_type_body_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env vt ty tb rt args a x b.
    compile_type_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env vt ty tb rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> dxrule ctor_expr_callback_first_emission >> disch_tac >>
  ntac 6 gen_tac >> Cases_on `tb`
  >~ [`Empty`] >- metis_tac[ctor_empty_type_dispatch_first_emission]
  >~ [`MaxValue`] >- metis_tac[ctor_maxvalue_type_dispatch_first_emission]
  >~ [`MinValue`] >- metis_tac[ctor_minvalue_type_dispatch_first_emission]
  >~ [`Epsilon`] >- metis_tac[ctor_epsilon_type_dispatch_first_emission]
  >~ [`Convert`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_convert_type_dispatch_first_emission >>
      disch_then irule >> metis_tac[])
  >~ [`Extract32`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_extract32_type_dispatch_first_emission >>
      disch_then irule >> metis_tac[])
  >~ [`AbiEncode _ _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_abi_encode_type_dispatch_first_emission >>
      disch_then irule >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_abi_decode_type_dispatch_first_emission >>
  disch_then irule >> metis_tac[]
QED

Theorem ctor_guarded_builtin_body_first_emission:
  (!e env ty a. expr_size e < bound ==> !x b.
    compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env rt ty bi args a x b.
    compile_builtin_dispatch_body (expr_child_callback bound compile_expr)
      env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 5 gen_tac >> Cases_on `bi`
  >~ [`Bop _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_bop_dispatch_first_emission >> disch_then irule >> metis_tac[])
  >~ [`Concat`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_concat_dispatch_first_emission >> disch_then irule >> metis_tac[])
  >~ [`MakeArray _ _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_make_array_dispatch_first_emission >> disch_then irule >> metis_tac[])
  >~ [`Uint2Str`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_uint2str_dispatch_first_emission >> disch_then irule >> metis_tac[])
  >~ [`AsWeiValue _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_as_wei_value_dispatch_first_emission >> disch_then irule >> metis_tac[])
  >~ [`ECRecover`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_bytes_precompile_dispatch_first_emission >> disch_then irule >> simp[] >> metis_tac[])
  >~ [`ECAdd`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_bytes_precompile_dispatch_first_emission >> disch_then irule >> simp[] >> metis_tac[])
  >~ [`ECMul`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_bytes_precompile_dispatch_first_emission >> disch_then irule >> simp[] >> metis_tac[])
  >~ [`MethodId`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_bytes_precompile_dispatch_first_emission >> disch_then irule >> simp[] >> metis_tac[])
  >~ [`Slice _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_bytes_precompile_dispatch_first_emission >> disch_then irule >> simp[] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >>
  drule_at (Pos last) ctor_guarded_scalar_dispatch_first_emission >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Theorem ctor_target_callback_first_emission:
  (!env ty e a x b. cfn env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !target env a x b. compile_get_target_ptr cfn env target a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> gen_tac >> measureInduct_on `base_assignment_target_size target` >> Cases_on `target` >> rpt gen_tac >> strip_tac
  >- metis_tac[ctor_name_target_first_emission]
  >- metis_tac[ctor_top_level_name_target_first_emission]
  >- (drule_at (Pos last) ctor_subscript_target_first_emission >> disch_then irule >>
      conj_tac >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.LESS_ADD_SUC, arithmeticTheory.ADD1]) >> metis_tac[]) >>
  drule_at (Pos last) ctor_attribute_target_first_emission >> disch_then irule >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.LESS_ADD_SUC, arithmeticTheory.ADD1]
QED

Theorem ctor_list_case_const[local]:
  !ls (v:'b). list_CASE (ls:'a list) v (\h t. v) = v
Proof
  Cases >> simp[]
QED

Theorem ctor_expr_case_const[local]:
  !e (v:'a). expr_CASE e (\a b. v) (\a b. v) (\a b c. v)
    (\a b c d. v) (\a b. v) (\a b c. v) (\a b c. v) (\a b c. v)
    (\a b c. v) (\a b c d. v) (\a b. v) (\a b c d. v) = v
Proof
  Cases >> simp[]
QED

Theorem ctor_builtin_body_state_pred[local]:
  (!ce rt ty bi args. P (SND (g ce rt ty bi args a))) /\
  (!ce rt at an bt bn mt mn. P (SND (compile_addmod_names ce rt at an bt bn mt mn a))) /\
  (!ce rt at an bt bn mt mn. P (SND (compile_mulmod_names ce rt at an bt bn mt mn a))) /\
  (!ce rt at an bt bn. P (SND (compile_powmod256_names ce rt at an bt bn a))) ==>
  !env ty ann bi args.
    P (SND (compile_expr_body f g h env ty (Builtin ann bi args) a))
Proof
  strip_tac >> ntac 4 gen_tac >> Cases_on `bi` >>
  ASM_SIMP_TAC (srw_ss()) [Once compile_expr_body_def, LET_THM,
    TypeBase.case_rand_of ``:'a list``, TypeBase.case_rand_of ``:expr``,
    ctor_list_case_const, ctor_expr_case_const]
QED

Theorem ctor_builtin_expr_first_emission:
  (!env rt ty bi args a x b. g env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty ann bi args a x b. compile_expr_body f g h env ty (Builtin ann bi args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 6 gen_tac >>
  qabbrev_tac `P = \b. cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))` >>
  `P (SND (compile_expr_body f g h env ty (Builtin ann bi args) a))`
    suffices_by (rpt strip_tac >> gvs[Abbr `P`]) >>
  irule ctor_builtin_body_state_pred >> rpt conj_tac
  >~ [`!ce rt ty bi args. P (SND (g ce rt ty bi args a))`]
  >- (rpt gen_tac >> Cases_on `g ce rt ty bi args a` >>
      gvs[Abbr `P`] >> metis_tac[])
  >~ [`!ce rt at an bt bn. P (SND (compile_powmod256_names ce rt at an bt bn a))`]
  >- (rpt gen_tac >> Cases_on `compile_powmod256_names ce rt at an bt bn a` >>
      gvs[Abbr `P`] >>
      irule (SRULE [Once compile_expr_body_def, LET_THM, vyperASTTheory.expr_type_def] ctor_powmod256_names_body_first_emission) >>
      goal_assum (drule_at Any))
  >~ [`!ce rt at an bt bn mt mn. P (SND (compile_mulmod_names ce rt at an bt bn mt mn a))`]
  >- (rpt gen_tac >> Cases_on `compile_mulmod_names ce rt at an bt bn mt mn a` >>
      gvs[Abbr `P`] >>
      irule (SRULE [Once compile_expr_body_def, LET_THM, vyperASTTheory.expr_type_def] ctor_mulmod_names_body_first_emission) >>
      goal_assum (drule_at Any)) >>
  rpt gen_tac >> Cases_on `compile_addmod_names ce rt at an bt bn mt mn a` >>
  gvs[Abbr `P`] >>
  irule (SRULE [Once compile_expr_body_def, LET_THM, vyperASTTheory.expr_type_def] ctor_addmod_names_body_first_emission) >>
  goal_assum (drule_at Any)
QED

Theorem ctor_guarded_expr_body_first_emission:
  !e.
  (!e' env ty a. expr_size e' < expr_size e ==> !x b.
    compile_expr env ty e' a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!args env rt ty bi a. list_size expr_size args < expr_size e ==> !x b.
    compile_builtin_dispatch env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!args env vt ty tb rt a. list_size expr_size args < expr_size e ==> !x b.
    compile_type_builtin_dispatch env vt ty tb rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !env ty a x b.
    compile_expr_body (expr_child_callback (expr_size e) compile_expr)
      (builtin_child_callback (expr_size e) compile_builtin_dispatch)
      (type_child_callback (expr_size e) compile_type_builtin_dispatch) env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> strip_tac >> Cases_on `e`
  >~ [`IfExp _ _ _ _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_ifexp_first_emission >> disch_then irule >> metis_tac[])
  >~ [`Attribute _ _ _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_attribute_body_guarded_first_emission >> disch_then irule >> metis_tac[])
  >~ [`Subscript _ _ _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_subscript_body_guarded_first_emission >> disch_then irule >> metis_tac[])
  >~ [`StructLit _ _ _`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_structlit_body_guarded_first_emission >> disch_then irule >> metis_tac[])
  >~ [`Builtin _ _ _`] >- (drule ctor_builtin_callback_first_emission >> disch_tac >>
      rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_builtin_expr_first_emission >>
      disch_then irule >> metis_tac[])
  >~ [`TypeBuiltin _ _ _ _`] >- (drule ctor_type_callback_first_emission >> disch_tac >>
      simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM,
        Excl "type_child_callback_def", Excl "expr_size_def"] >> metis_tac[])
  >~ [`Name _ _`] >- (simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >> metis_tac[ctor_name_vv_first_emission])
  >~ [`Literal _ _`] >- (simp_tac (srw_ss()) [Once compile_expr_body_def, LET_THM] >> metis_tac[ctor_literal_vv_first_emission])
  >~ [`FlagMember _ _ _`] >- metis_tac[ctor_flag_member_first_emission]
  >~ [`TopLevelName _ _`] >- metis_tac[ctor_top_level_name_first_emission]
  >~ [`Pop _ _`] >- (drule ctor_expr_callback_first_emission >> disch_tac >>
      drule ctor_target_callback_first_emission >> disch_tac >> rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_pop_body_first_emission >> disch_then irule >> metis_tac[])
  >> Cases_on `c`
  >~ [`RawLog`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_real_system_expr_first_emission >>
      disch_then irule >> gvs[] >> metis_tac[])
  >~ [`RawRevert`] >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_real_system_expr_first_emission >>
      disch_then irule >> gvs[] >> metis_tac[])
  >~ [`Send _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_send_expr_first_emission >> disch_then irule >> metis_tac[])
  >~ [`IntCall _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_int_call_expr_first_emission >> disch_then irule >> metis_tac[])
  >~ [`RawCallTarget _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_raw_call_expr_first_emission >> disch_then irule >> metis_tac[])
  >~ [`RawCallCalldataTarget _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_raw_call_calldata_expr_first_emission >> disch_then irule >> metis_tac[])
  >~ [`CreateTarget _ _ _ _`] >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_guarded_create_call_expr_first_emission >> disch_then irule >> metis_tac[])
  >~ [`ExtCall _ _ sig _`] >- (PairCases_on `sig` >> rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_guarded_ext_call_expr_first_emission >> disch_then irule >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_invalid_call_expr_first_emission_strong >>
  simp[] >> metis_tac[]
QED

Theorem ctor_compile_expr_first_emission_mutual:
  (!env ty e a. !x b. compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!env rt ty bi args a. !x b. compile_builtin_dispatch env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!env vt ty tb rt args a. !x b. compile_type_builtin_dispatch env vt ty tb rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [Once compile_expr_raw_def] >>
  simp_tac (srw_ss()) [SF ETA_ss] >> rpt gen_tac >> strip_tac
  >- (drule_at (Pos last) ctor_guarded_expr_body_first_emission >> disch_then irule >> metis_tac[])
  >- (drule_at (Pos last) ctor_guarded_builtin_body_first_emission >> disch_then irule >> metis_tac[]) >>
  drule_at (Pos last) ctor_guarded_type_body_first_emission >> disch_then irule >> metis_tac[]
QED

Theorem ctor_compile_expr_first_emission:
  !env ty e a x b. compile_expr env ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  metis_tac[cj 1 ctor_compile_expr_first_emission_mutual]
QED

Theorem ctor_compile_builtin_dispatch_first_emission:
  !env rt ty bi args a x b. compile_builtin_dispatch env rt ty bi args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  metis_tac[cj 2 ctor_compile_expr_first_emission_mutual]
QED

Theorem ctor_compile_type_builtin_dispatch_first_emission:
  !env vt ty tb rt args a x b. compile_type_builtin_dispatch env vt ty tb rt args a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  metis_tac[cj 3 ctor_compile_expr_first_emission_mutual]
QED
