(* Direct memory-return stores, with their actual counted ghost endpoint. *)
Theory internalReturnStorePtr
Ancestors assignBasePtrCopyPath assignBasePtrBytesPost typedMemoryCopy
  bodyPtrDefs fragExecPtr fragGasPathPtr gasPathPtrExec context emitHelper emitHelperProps
  venomState venomExecSemantics venomInst ptrDiscipline words list
  valueEncoding finite_map exprLoweringProps valueCopy compileEnv

Theorem internal_return_store_path_ptr:
  !ce src dst ty sty sa sb fn s a d len n G tn D ctx PG tv v.
    compile_store_memory ce (Var src) (Var dst) ty sty sa = ((),sb) /\
    ~is_word_type ty /\ (ty = sty \/ is_bytestring_type ty) /\
    n = (if is_bytestring_type ty then 32 + 32 * word_size len
         else type_memory_bytes ce ty) /\ n < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    (is_bytestring_type ty ==>
      mload (w2n a) s = n2w len /\ ptr_covers G tn src s 32 /\
      (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)) /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      typed_copy_state_frame sa (w2n d) n s u /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule assign_base_store_bytestring_robust_counted >>
      disch_then drule >>
      disch_then (qspec_then `s` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `len` mp_tac) >>
      disch_then (drule_all o SRULE []) >>
      disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`Gf`, `tf`, `u`] >> simp[]) >>
  `ty = sty` by metis_tac[] >> gvs[compile_store_memory_def] >>
  Cases_on `type_memory_bytes ce sty = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >> rpt strip_tac >>
      irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
  `0 < type_memory_bytes ce sty` by decide_tac >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `type_memory_bytes ce sty` >>
     gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  simp[typed_copy_mcopy_state_frame] >>
  simp[step_taint_def, step_prov_def, set_prov_def, out_prov_def,
       mk_inst_def, set_var_taint_def, imm_taint_def, op_taint_def,
       lookup_var_def, mcopy_def, write_memory_with_expansion_def,
       adopt_reset_def, store_taint_def, DRESTRICT_UNIV]
QED

Theorem internal_return_store_frag_ptr:
  !ce src dst ty sty sa sb cx ctx PG s a d len n G tn tv v rpc pc.
    compile_store_memory ce (Var src) (Var dst) ty sty sa = ((),sb) /\
    ~is_word_type ty /\ (ty = sty \/ is_bytestring_type ty) /\
    n = (if is_bytestring_type ty then 32 + 32 * word_size len
         else type_memory_bytes ce ty) /\ n < dimword (:256) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    (is_bytestring_type ty ==>
      mload (w2n a) s = n2w len /\ ptr_covers G tn src s 32 /\
      (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)) /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) /\
    stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
    lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} ==>
    frag_exec_ptr cx ctx PG sa sb
      (\H tm t. H = G /\ tm = tn /\ t = s)
      (\H tm t. typed_copy_state_frame sa (w2n d) n s t /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
             val_in_memory tv v (w2n d) m) /\
        stor_taint_ok cx tm t /\ lookup_var rpc t = SOME pc /\
        op_taint tm (Var rpc) = {})
      (\gh r. F)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[frag_exec_ptr_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(\H tm t. _) _ _ _` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  rpt (qpat_x_assum `_ = s` SUBST_ALL_TAC) >>
  rpt (qpat_x_assum `_ = G` SUBST_ALL_TAC) >>
  rpt (qpat_x_assum `_ = tn` SUBST_ALL_TAC) >>
  drule_all internal_return_store_path_ptr >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
      simp[typed_copy_state_frame_def, venom_state_component_equality] >>
      strip_tac >> gvs[stor_taint_ok_def]) >>
  drule gas_path_ptr_exec >> simp[fragExecTheory.exit_result_def] >>
  strip_tac >> metis_tac[]
QED
