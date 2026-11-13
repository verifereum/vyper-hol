(* Task-owned allocation adapter. Re-executed allocation sites are allowed. *)
Theory externalReturnCopyAlloc
Ancestors
  externalReturnCopyRecursive externalReturnCopyAdapter exprSimAlloc
  localPtrsProps exprLoweringProps loweringSlice compileEnv loweringStateRelDefs
  externalReturnCopyFrame valueEncodingProps venomState fragExec

Theorem return_alloc_local_region_frame:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  (local_region cenv scopes t name b sz <=>
   local_region cenv scopes s name b sz)
Proof
  rw[local_region_def] >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* The ownership witness concerns the actual readable extent, not capacity.
   An old allocation id is distinct from the new site even on reuse. *)
Theorem return_alloc_source_separation:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint dst dlen b len) /\
  (!name b len. local_region cenv es.scopes u name b len ==>
    regions_disjoint dst dlen b len) /\
  (0 < extent ==>
    (?aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      b <= src /\ src + extent <= b + len) \/
    (?name b len. local_region cenv es.scopes s name b len /\
      b <= src /\ src + extent <= b + len)) ==>
  (0 < extent ==> src + extent <= dst \/ dst + dlen <= src)
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `0 < extent ==> _` drule >> strip_tac
  >- (qpat_x_assum `!aid b len. _` drule_all >>
      simp[regions_disjoint_def] >> decide_tac) >>
  `local_region cenv es.scopes u name b len` by
    metis_tac[return_alloc_local_region_frame] >>
  qpat_x_assum `!name b len. _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem return_alloc_normalize_copy:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  return_copy_entry cenv ctx (get_tenv cx) dty sty dtv stv v /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv v ==>
    w2n sw + val_footprint stv v < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) /\
       b <= w2n sw /\ w2n sw + val_footprint stv v <= b + len) \/
     (?name b len. local_region cenv es.scopes s name b len /\
       b <= w2n sw /\ w2n sw + val_footprint stv v <= b + len))) ==>
  ?u w.
    frag_exec ctx sa sm (\z. z = s) (\z. z = u) (\r. F) /\
    stmt_state_rel ctx func cenv cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
    w2n w + type_memory_size dtv < dimword (:256) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    frag_exec ctx sm sb (\z. z = u)
      (\t. val_in_memory dtv v (w2n w) t.vs_memory /\
        return_copy_frame sm (w2n w) (type_memory_size dtv) u t) (\r. F)
Proof
  strip_tac >> drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `\r. F` strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`type_memory_size dtv`, `sa`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `0 < val_footprint stv v ==>
    w2n sw + val_footprint stv v <= w2n w \/
    w2n w + type_memory_size dtv <= w2n sw` by
    (strip_tac >> irule return_alloc_source_separation >>
     (conj_tac >- simp[]) >> qexistsl_tac [`cenv`, `es`, `s`, `sa`, `u`] >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  irule return_copy_entry_actual_footprint >>
  qpat_assum `return_copy_entry _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`sw`, `src`, `buf.buf_operand`] >> simp[]
QED

Theorem return_copy_local_ptrs_frame:
  return_copy_frame sa b sz s t /\ local_ptrs_reserved cenv sa /\
  local_ptrs_rel func cenv scopes s /\
  (!name lb len. local_region cenv scopes s name lb len ==>
    regions_disjoint b sz lb len) ==>
  local_ptrs_rel func cenv scopes t
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    gvs[return_copy_frame_def, venomStateTheory.venom_state_component_equality] >>
  irule local_ptrs_rel_frame >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule memoryValueFrameTheory.memory_value_rel_mem_agree_region >>
      simp[] >> qexistsl_tac [`type_memory_size entry.type`, `s.vs_memory`] >>
      simp[] >>
      `local_region cenv scopes s name (w2n w) sz'` by
        (simp[local_region_def] >> metis_tac[]) >>
      qpat_x_assum `!name lb len. _` drule >>
      gvs[regions_disjoint_def, return_copy_frame_def,
          return_copy_memory_frame_def] >>
      strip_tac >> sym_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def, return_copy_frame_def] >>
  metis_tac[]
QED

Theorem return_copy_immutables_frame:
  return_copy_frame sa b sz s t /\
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  strip_tac >>
  `t.vs_data_section = s.vs_data_section` by
    gvs[return_copy_frame_def, venom_state_component_equality] >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >>
  gvs[return_copy_frame_def, return_copy_memory_frame_def,
      stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
  first_x_assum irule >> gvs[regions_disjoint_def] >> decide_tac
QED

Theorem return_copy_stmt_state_frame:
  return_copy_frame sa b sz s t /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb len. local_region cenv es.scopes s name lb len ==>
    regions_disjoint b sz lb len) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels` by
    gvs[return_copy_frame_def, venom_state_component_equality] >>
  `!name b sz. local_region cenv es.scopes t name b sz <=>
    local_region cenv es.scopes s name b sz` by
    metis_tac[return_alloc_local_region_frame, return_copy_frame_def] >>
  irule stmt_state_rel_allocas_frame >> rpt conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      gvs[stmt_state_rel_def, local_ptrs_reserved_def, return_copy_frame_def] >>
      metis_tac[])
  >- (irule immutable_alloca_sep_fields >>
      qexistsl_tac [`s`, `es`] >> gvs[stmt_state_rel_def] >> metis_tac[])
  >- (irule state_rel_frame >> conj_tac
      >- (`local_ptrs_rel func cenv es.scopes s` by
            gvs[stmt_state_rel_def, state_rel_def] >>
          drule_all return_copy_local_ptrs_frame >> simp[]) >>
      qexistsl_tac [`es`, `s`] >>
      `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
        (drule_all return_copy_immutables_frame >> simp[]) >>
      gvs[stmt_state_rel_def, return_copy_frame_def, venom_state_component_equality]) >>
  qexistsl_tac [`es`, `s`] >> simp[]
QED

Theorem return_alloc_copy_post:
  return_copy_frame sm (w2n w) sz u t /\
  stmt_state_rel ctx func cenv cx es u /\
  local_ptrs_reserved cenv sm /\
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  eval_operand buf.buf_operand u = SOME w /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
  (!name lb len. local_region cenv es.scopes u name lb len ==>
    regions_disjoint (w2n w) sz lb len) ==>
  stmt_state_rel ctx func cenv cx es t /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u)
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule return_copy_stmt_state_frame >>
     qpat_assum `return_copy_frame _ _ _ _ _` (irule_at Any) >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]` >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  `?p. buf.buf_operand = Var p /\ not_fresh_at sm p` by
    (gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  gvs[return_copy_frame_def, venom_state_component_equality, eval_operand_def] >>
  metis_tac[]
QED

Theorem return_normalize_actual_frag:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  return_copy_entry cenv ctx (get_tenv cx) dty sty dtv stv v /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv v ==>
    w2n sw + val_footprint stv v < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) /\
       b <= w2n sw /\ w2n sw + val_footprint stv v <= b + len) \/
     (?name b len. local_region cenv es.scopes s name b len /\
       b <= w2n sw /\ w2n sw + val_footprint stv v <= b + len))) ==>
  frag_exec ctx sa sb (\z. z = s)
    (\t. ?w. stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) (\r. F)
Proof
  strip_tac >> drule_all return_alloc_normalize_copy >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`type_memory_size dtv`, `sa`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `cs_extends sa sm` by
    (qspecl_then [`type_memory_size dtv`, `sa`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `cs_extends sm sb` by
    (`ci_mono sm (SND (compile_store_memory_typed cenv buf.buf_operand dty src sty sm))`
       by simp[cj 1 ci_mono_typed_memory_family] >> gvs[ci_mono_def]) >>
  qpat_assum `frag_exec ctx sa sm _ _ _` (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> simp[] >>
  drule frag_exec_weaken >> disch_then irule >> simp[] >>
  rpt strip_tac >>
  drule_all return_alloc_copy_post >> strip_tac >>
  qexists_tac `w` >> simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem return_expr_normalize_source:
  expr_val_at cenv cx sty se sa es v src s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  stmt_state_rel ctx func cenv cx es s /\ eval_operand src s = SOME sw ==>
  (0 < val_footprint stv v ==>
    w2n sw + val_footprint stv v < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) /\
       b <= w2n sw /\ w2n sw + val_footprint stv v <= b + len) \/
     (?name b len. local_region cenv es.scopes s name b len /\
       b <= w2n sw /\ w2n sw + val_footprint stv v <= b + len)))
Proof
  strip_tac >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s /\
   alloca_room ctx func s` by gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all externalReturnFootprintTheory.return_expr_window_frontier >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  conj_tac >- (gvs[] >> decide_tac) >>
  gvs[loweringPostsTheory.expr_val_at_def] >> metis_tac[]
QED

(* Consumer boundary: rank-free recursive copying plus actual expression
   ownership. Neither fresh allocation ids nor source capacity are premises. *)
Theorem return_normalize_expr_frag:
  compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  ~is_word_type sty /\ expr_val_at cenv cx sty se sa es v src s ==>
  frag_exec ctx sa sb (\z. z = s)
    (\t. ?w. stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) (\r. F)
Proof
  strip_tac >>
  `return_copy_entry cenv ctx (get_tenv cx) dty sty dtv stv v` by
    (irule return_copy_recursive_entry >> simp[] >> metis_tac[]) >>
  `cs_extends sa sm` by
    (qspecl_then [`type_memory_bytes cenv dty`, `sa`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `cs_extends sm sb` by
    (`ci_mono sm (SND (compile_store_memory_typed cenv buf.buf_operand dty src sty sm))`
       by simp[cj 1 ci_mono_typed_memory_family] >> gvs[ci_mono_def]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  irule return_normalize_actual_frag >>
  qpat_assum `return_copy_entry _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`sw`, `src`, `sm`] >> simp[] >>
  (conj_tac >- metis_tac[]) >> strip_tac >>
  drule_all return_expr_normalize_source >> simp[]
QED
