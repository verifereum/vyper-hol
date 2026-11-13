(* Runtime-sized equal-layout dynamic payload copying. *)
Theory annAssignTypedCopyDynamicBulkPtr
Ancestors
  assignBasePtrStoragePath typedCopyLoopHeaderPtr annAssignPtrCopy
  assignBasePtrMcopyTransport fragGasPathPtr bodyPtrDefs
  venomState venomExecSemantics venomInst ptrDiscipline finite_map
  words arithmetic list pred_set robustCopyTransportPtr valueEncodingProps
  valueEncodingProofs typedMemoryCopy typedCopyPtr typedNormalizeDynarray
  context compileEnv emitHelper fragExec rich_list

Theorem annassign_dynamic_bulk_exact_counted:
  !s fn bb id len sz tmp dst src a b n tn G ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var len;Lit (n2w sz)] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) MCOPY [Var dst;Var src;Var tmp] []) /\
    lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    src <> tmp /\ dst <> tmp /\ n * sz < dimword (:256) /\
    ptr_covers G tn src s (n * sz) /\ ptr_covers G tn dst s (n * sz) ==>
    ?s1 g1 t1 u tf.
      s1 = (update_var tmp (n2w (n * sz)) s with
        vs_inst_idx := SUC s.vs_inst_idx) /\
      g1 = DRESTRICT G (COMPL {tmp}) /\
      t1 = (tn with t_var := tn.t_var |+ (tmp,{})) /\
      u = mcopy (w2n b) (w2n a) (n * sz) s1 /\
      tf = step_taint (mk_inst (id+1) MCOPY [Var dst;Var src;Var tmp] [])
        s1 u t1 /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tf
        (OK (u with vs_inst_idx := s.vs_inst_idx+2))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v = update_var tmp (n2w (n * sz)) s` >>
  `step_inst_base (mk_inst id MUL [Var len;Lit (n2w sz)] [tmp]) s = OK v` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >>
     simp[Abbr `v`, exec_pure2_def, eval_operand_def, word_mul_n2w]) >>
  `step_prov PG G (mk_inst id MUL [Var len;Lit (n2w sz)] [tmp]) v =
     DRESTRICT G (COMPL {tmp}) /\
   step_taint (mk_inst id MUL [Var len;Lit (n2w sz)] [tmp]) s v tn =
     (tn with t_var := tn.t_var |+ (tmp,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >>
     simp[Abbr `v`, update_var_def] >> rw[] >> gvs[op_taint_def]) >>
  qabbrev_tac `s1 = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {tmp})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (tmp,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (mp_tac (Q.SPECL [`s`,`fn`,`bb`,`id`,`MUL`,`Var len`,
       `Lit (n2w sz)`,`tmp`,`n2w (n * sz)`,`tn`,`G`,`ctx`,`D`,`PG`]
       assign_base_copy_binop_counted) >>
     simp[GSYM (markerTheory.Abbrev_def), Abbr `s1`, Abbr `v`, op_taint_def]) >>
  qabbrev_tac `u = mcopy (w2n b) (w2n a) (n * sz) s1` >>
  qabbrev_tac `tf = step_taint
    (mk_inst (id+1) MCOPY [Var dst;Var src;Var tmp] []) s1 u t1` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g1 tf
    (OK (u with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (simp[Abbr `tf`, Abbr `u`] >> irule annassign_mcopy_path_ptr >>
     simp[Abbr `s1`, Abbr `v`, Abbr `g1`, Abbr `t1`,
       update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
       op_taint_def, w2n_n2w, LESS_MOD] >>
     gvs[ptr_covers_def, FLOOKUP_DRESTRICT, op_taint_def, lookup_var_def,
       FLOOKUP_UPDATE]) >>
  `SUC s1.vs_inst_idx = s.vs_inst_idx+2` by
    simp[Abbr `s1`, ADD1] >>
  `gas_path_ptr D 0 ctx fn PG G tn s (0+0) g1 tf
    (OK (u with vs_inst_idx := s.vs_inst_idx+2))` by
    (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> gvs[]) >>
  qexistsl_tac [`s1`,`g1`,`t1`,`u`,`tf`] >>
  gvs[Abbr `s1`, Abbr `v`, Abbr `g1`, Abbr `t1`, Abbr `u`, Abbr `tf`]
QED

Theorem annassign_robust_indexed_copy_window:
  !tv f N src dst tn tn' mem mem'.
    mem_bytes_at dst (N * type_memory_size tv) mem' =
      mem_bytes_at src (N * type_memory_size tv) mem /\
    (!j. j < N * type_memory_size tv ==>
      (dst+j IN tn' <=> src+j IN tn)) /\
    (!i. i < N ==> val_wf tv (f i)) /\
    (!i. i < N ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory tv (f i) (src + i * type_memory_size tv) m) ==>
    !i. i < N ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory tv (f i) (dst + i * type_memory_size tv) m
Proof
  rpt strip_tac >> drule_all copied_window_agree_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_wf tv (f i) /\
   val_in_memory tv (f i) (src + i * type_memory_size tv) mix` by
    metis_tac[] >>
  irule val_in_memory_relocate >> simp[] >>
  qexistsl_tac [`mix`, `type_memory_size tv`, `src + i * type_memory_size tv`] >>
  simp[] >>
  irule mem_bytes_at_translated_window >>
  qexists_tac `N * type_memory_size tv` >> simp[] >>
  `SUC i <= N` by decide_tac >>
  irule LESS_EQ_TRANS >> qexists_tac `SUC i * type_memory_size tv` >>
  simp[MULT_CLAUSES]
QED

Theorem annassign_dynamic_bulk_endpoint:
  !s s1 u tf tn t1 G g1 sa tmp n sz a b id src dst tv f ix.
    s1 = (update_var tmp (n2w (n * sz)) s with
      vs_inst_idx := SUC s.vs_inst_idx) /\
    g1 = DRESTRICT G (COMPL {tmp}) /\
    t1 = (tn with t_var := tn.t_var |+ (tmp,{})) /\
    u = mcopy (w2n b) (w2n a) (n * sz) s1 /\
    tf = step_taint (mk_inst id MCOPY [Var dst;Var src;Var tmp] []) s1 u t1 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    src <> tmp /\ dst <> tmp /\ n * sz < dimword (:256) /\
    ~not_fresh_at sa tmp /\ sz = type_memory_size tv /\
    (!i. i < n ==> val_wf tv (f i)) /\
    (!i. i < n ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv (f i) (w2n a + i * sz) m) ==>
    typed_copy_state_frame sa (w2n b) (n * sz) s
      (u with vs_inst_idx := ix) /\
    (!i. i < n ==> !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory tv (f i) (w2n b + i * sz) m) /\
    (!j. ~(w2n b <= j /\ j < w2n b + n * sz) ==>
      mem_bytes_at j 1 u.vs_memory = mem_bytes_at j 1 s.vs_memory /\
      (j IN tf.t_mem <=> j IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x <> tmp ==>
      lookup_var x (u with vs_inst_idx := ix) = lookup_var x s /\
      FLOOKUP g1 x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var dst) s1 = SOME b /\
   eval_operand (Var src) s1 = SOME a /\
   eval_operand (Var tmp) s1 = SOME (n2w (n * sz))` by
    gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `u = mcopy (w2n b) (w2n a) (w2n (n2w (n * sz):bytes32)) s1` by simp[] >>
  drule_all (Q.SPECL [`Var dst`,`Var src`] assign_base_mcopy_taint_window) >>
  strip_tac >>
  drule_all (Q.SPECL [`Var dst`,`Var src`] assign_base_mcopy_endpoint_frame) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `s1` >>
      reverse conj_tac
      >- gvs[typed_copy_mcopy_state_frame] >>
      gvs[typed_copy_state_frame_def, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `sz = _` SUBST_ALL_TAC >>
      match_mp_tac annassign_robust_indexed_copy_window >>
      qexistsl_tac [`w2n a`,`tn.t_mem`,`s.vs_memory`] >>
      gvs[mcopy_mem_bytes_at_same, update_var_def]) >>
  conj_tac
  >- (gen_tac >> disch_tac >> conj_tac
      >- (`s1.vs_memory = s.vs_memory` by simp[update_var_def] >>
          qpat_x_assum `s1.vs_memory = _`
            (fn th => pure_rewrite_tac[GSYM th]) >>
          qpat_assum `u = mcopy _ _ (n * sz) s1` (fn th => rewrite_tac[th]) >>
          irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
      gvs[] >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  gvs[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    op_taint_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem annassign_dynamic_bulk_resources:
  !s fn bb id len sz tmp dst src a b n tn G ctx D PG sa tv f.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var len;Lit (n2w sz)] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) MCOPY [Var dst;Var src;Var tmp] []) /\
    lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    src <> tmp /\ dst <> tmp /\ n * sz < dimword (:256) /\
    ptr_covers G tn src s (n * sz) /\ ptr_covers G tn dst s (n * sz) /\
    ~not_fresh_at sa tmp /\ sz = type_memory_size tv /\
    (!i. i < n ==> val_wf tv (f i)) /\
    (!i. i < n ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv (f i) (w2n a + i * sz) m) ==>
    ?H tf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
      ~t.vs_halted /\ typed_copy_state_frame sa (w2n b) (n * sz) s t /\
      (!i. i < n ==> !m. mem_agree_outside tf.t_mem t.vs_memory m ==>
        val_in_memory tv (f i) (w2n b + i * sz) m) /\
      (!j. ~(w2n b <= j /\ j < w2n b + n * sz) ==>
        mem_bytes_at j 1 t.vs_memory = mem_bytes_at j 1 s.vs_memory /\
        (j IN tf.t_mem <=> j IN tn.t_mem)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. x <> tmp ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_dynamic_bulk_exact_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  drule_all annassign_dynamic_bulk_endpoint >>
  disch_then (qspec_then `s.vs_inst_idx+2` strip_assume_tac) >>
  qexistsl_tac [`g1`,`tf`,`u with vs_inst_idx := s.vs_inst_idx+2`] >>
  gvs[] >> gvs[]
QED

Theorem annassign_dynamic_fast_compiler_suffix:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+9 /\
  DROP (LENGTH sa.cs_current_insts+7) sb.cs_current_insts =
    [mk_inst (sa.cs_next_id+7) MUL
      [Var ("%" ++ toString sa.cs_next_var);Lit (n2w (type_memory_bytes ce ty))]
      ["%" ++ toString (sa.cs_next_var+5)];
     mk_inst (sa.cs_next_id+8) MCOPY
      [Var ("%" ++ toString (sa.cs_next_var+4));
       Var ("%" ++ toString (sa.cs_next_var+3));
       Var ("%" ++ toString (sa.cs_next_var+5))] []]
Proof
  pure_rewrite_tac[Once compile_store_memory_typed_def, LET_THM] >> BETA_TAC >>
  ntac 7 (once_rewrite_tac[dyn_prefix_bind_op, dyn_prefix_bind_void] >>
    simp_tac (srw_ss()) [ADD_ASSOC, APPEND_ASSOC]) >>
  simp[compile_copy_memory_dynamic_def, dyn_prefix_bind_op,
    emit_void_def, fresh_id_def, emit_def, comp_ignore_bind_def,
    comp_return_def, comp_bind_def, ADD_ASSOC, APPEND_ASSOC] >>
  strip_tac >> gvs[] >> simp[DROP_APPEND, DROP_DROP, ADD_ASSOC]
QED

Theorem annassign_dynamic_fast_payload_locations:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts+7) =
      SOME (mk_inst (sa.cs_next_id+7) MUL
        [Var ("%" ++ toString sa.cs_next_var);Lit (n2w (type_memory_bytes ce ty))]
        ["%" ++ toString (sa.cs_next_var+5)]) /\
    get_instruction bb (LENGTH sa.cs_current_insts+8) =
      SOME (mk_inst (sa.cs_next_id+8) MCOPY
        [Var ("%" ++ toString (sa.cs_next_var+4));
         Var ("%" ++ toString (sa.cs_next_var+3));
         Var ("%" ++ toString (sa.cs_next_var+5))] [])
Proof
  strip_tac >> drule annassign_dynamic_fast_compiler_suffix >> strip_tac >>
  `EL (LENGTH sa.cs_current_insts+7) sb.cs_current_insts =
    mk_inst (sa.cs_next_id+7) MUL
      [Var ("%" ++ toString sa.cs_next_var);Lit (n2w (type_memory_bytes ce ty))]
      ["%" ++ toString (sa.cs_next_var+5)]` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[listTheory.EL_DROP]) >>
  `EL (LENGTH sa.cs_current_insts+8) sb.cs_current_insts =
    mk_inst (sa.cs_next_id+8) MCOPY
      [Var ("%" ++ toString (sa.cs_next_var+4));
       Var ("%" ++ toString (sa.cs_next_var+3));
       Var ("%" ++ toString (sa.cs_next_var+5))] []` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `EL 1`) >>
     simp[listTheory.EL_DROP, ADD_ASSOC]) >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[get_instruction_def, EL_APPEND1]
QED
