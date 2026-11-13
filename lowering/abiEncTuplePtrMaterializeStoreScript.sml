(* Physical bytestring capacities do not change pointer representations. *)
Theory abiEncTuplePtrMaterializeStore
Ancestors
  assignTuplePtrLocalCompat abiEncodeMaterialize bodyPtrDefs
  valueCopyBytes valueEncodingDefs valueEncodingProps compileEnv context
  vyperValue vyperTyping loweringPosts exprSimProps
  assignBasePtrStaging assignBasePtrMcopyGhost revertReasonCopyPtr
  typedCopyPtr venomState venomExecSemantics venomInst ptrDiscipline
  allocationPtr fragGasPathPtr finite_map words wordArgsPtr
  exprSimBufferStore exprLoweringProps loweringStateRelDefs

Theorem materialize_bytestring_ptr_layout:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  is_bytestring_type dt /\ evaluate_type (get_tenv cx) dt = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v /\
  ptr_val_ok cx ty v op G tn s ==>
  ptr_val_ok cx dt v op G tn s
Proof
  strip_tac >>
  `~is_word_type ty /\ ~is_word_type dt` by
    metis_tac[is_bytestring_word_type] >>
  `(?n. tv = BaseTV (StringT n)) \/
   (?n. tv = BaseTV (BytesT (Dynamic n)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  `(?n. dtv = BaseTV (StringT n)) \/
   (?n. dtv = BaseTV (BytesT (Dynamic n)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def] >> rpt strip_tac
  >- metis_tac[bytestring_robust_representation_compat_ptr] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_footprint_def, val_store_size_def, val_in_memory_def]
QED

(* Fixed-layout stores preserve capacity, not merely the copied footprint. *)
Theorem materialize_fixed_store_owned_ptr:
  compile_store_memory ce (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  n = type_memory_bytes ce ty /\ n < dimword (:256) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
  ptr_covers G tn src s n /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) /\
  local_ptrs_rel fn ce es.scopes s /\ ghost_inv d ce cx es G tn s /\
  (!name base sz. local_region ce es.scopes s name base sz ==>
    regions_disjoint (w2n b) n base sz) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < fr.cs_next_id ==> regions_disjoint (w2n b) n off sz) ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u = (if n = 0 then s else
      mcopy (w2n b) (w2n a) n s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ghost_inv d ce cx es H tf u /\ ghost_kept ce es fr G tn s H tf /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers H tf p u k) /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_prev_bb = s.vs_prev_bb /\
    (!q. eval_operand q u = eval_operand q s) /\
    (!name base sz. local_region ce es.scopes u name base sz <=>
      local_region ce es.scopes s name base sz)
Proof
  strip_tac >>
  `compile_copy_memory (Var dst) (Var src) n sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl [`G`, `tn`] >> simp[cj 1 gas_path_ptr_rules, ghost_kept_refl] >>
      rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
  qabbrev_tac `u = mcopy (w2n b) (w2n a) n s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `H = step_prov PG G
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
    (mcopy (w2n b) (w2n a) n s)` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
    s (mcopy (w2n b) (w2n a) n s) tn` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    ghost_inv d ce cx es H tf u /\ ghost_kept ce es fr G tn s H tf` by
    (irule assign_base_copy_memory_ghost_endpoint_ptr >>
     simp[Abbr `u`, Abbr `H`, Abbr `tf`] >> metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `sa.cs_current_bb = sb.cs_current_bb` by
    (drule buffer_copy_memory_shape >> simp[same_blocks_def]) >>
  `!p k. ptr_covers G tn p s k ==> ptr_covers H tf p u k` by
    (rpt strip_tac >>
     simp[Abbr `u`, Abbr `H`, Abbr `tf`, ptr_covers_def,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, mk_inst_def, op_taint_def, DRESTRICT_UNIV,
          mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
     gvs[ptr_covers_def, op_taint_def, lookup_var_def]) >>
  qexistsl [`H`, `tf`, `u`] >> simp[] >>
  simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def,
       eval_operand_def, lookup_var_def, local_region_def] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED
