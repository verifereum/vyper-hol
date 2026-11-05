(* Initialized immutable windows survive allocation-backed LocCode copies. *)
Theory bodyIntCallWindowCodeCopy
Ancestors
  bodyIntCallFreshCodeCopy bodyIntCallImmutableLifetime exprSimHash
  exprLoweringProps compileEnv loweringHalt fragExec context exprSimCopy
  bodyIntCallImmutableCopyPath

Theorem initialized_immutable_alloca_window:
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) name =
    SOME (itv,iv) ==>
  off + type_memory_size itv <= LENGTH s.vs_memory /\
  regions_disjoint off (type_memory_size itv) b sz
Proof
  simp[stmt_state_rel_def, state_rel_def, immutables_rel_def,
       immutable_alloca_sep_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem alloc_buffer_inst_member:
  compile_alloc_buffer sz sa = (buf,mid) /\ fn_has_code sa mid func ==>
  ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_id = sa.cs_next_id
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (emitted_insts sa mid)` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  drule_all hash_emitted_inst_mem >> strip_tac >>
  goal_assum drule >> simp[venomInstTheory.mk_inst_def]
QED

Theorem allocated_imm_copy_windows:
  compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca src dst n 0 mid =
    ((),sb) /\ copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,32*n) /\
  w2n w + 32*n < dimword (:256) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand mid region) ==>
  ?t. copy_runtime_frame mid s sb t /\
    (cenv.ce_is_ctor ==> !name off itv iv.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) name =
        SOME (itv,iv) ==>
      mem_bytes_at off (type_memory_size itv) t.vs_memory =
        mem_bytes_at off (type_memory_size itv) s.vs_memory)
Proof
  strip_tac >>
  `cenv.ce_is_ctor ==> !region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >> fs[stmt_state_rel_def, immutable_base_zero_def] >> metis_tac[]) >>
  `?t. copy_runtime_frame mid s sb t /\
       t.vs_memory =
         (immutable_transfers F cenv.ce_is_ctor a w n 0 s).vs_memory` by
    (Cases_on `cenv.ce_is_ctor` >> gvs[] >-
       (drule_all copy_ctor_run >> simp[]) >>
     drule_all copy_runtime_run >> simp[]) >>
  qexists `t` >> simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all initialized_immutable_alloca_window >> strip_tac >>
  irule (cj 1 immutable_transfers_window) >> simp[]
QED

Theorem loccode_copy_windows_run:
  compile_ensure_in_memory src LocCode sz wc cenv.ce_is_ctor
    cenv.ce_imm_alloca sa = (dst,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand sa region) /\
  0 < sz /\ sz < dimword (:256) /\ sz MOD 32 = 0 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (cenv.ce_is_ctor ==> !name off itv iv.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) name =
        SOME (itv,iv) ==>
      mem_bytes_at off (type_memory_size itv) t.vs_memory =
        mem_bytes_at off (type_memory_size itv) s.vs_memory)
Proof
  strip_tac >> drule loccode_copy_split >> strip_tac >>
  drule_all loccode_copy_code_split >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by fs[copy_old_operand_def] >>
  drule_all runtime_code_copy_alloc_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa mid) s = OK u` >>
  drule_all alloc_buffer_inst_member >> strip_tac >>
  `32*((sz+31) DIV 32) = sz` by simp[aligned_copy_size] >>
  `copy_old_operand mid src` by (irule copy_old_operand_mono >> qexists `sa` >> simp[]) >>
  `copy_old_operand mid buf.buf_operand` by gvs[copy_old_operand_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand mid region` by
    (rpt strip_tac >> irule copy_old_operand_mono >> qexists `sa` >> simp[]) >>
  `?t. copy_runtime_frame mid u sb t /\
    (cenv.ce_is_ctor ==> !name off itv iv.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) name =
        SOME (itv,iv) ==>
      mem_bytes_at off (type_memory_size itv) t.vs_memory =
        mem_bytes_at off (type_memory_size itv) u.vs_memory)` by
    (irule allocated_imm_copy_windows >> simp[] >>
     goal_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
     qexistsl [`a`, `ctx`, `func`, `inst`, `w`] >> simp[]) >>
  qexists `t` >> fs[copy_runtime_frame_def] >>
  drule_all emitted_insts_append >> strip_tac >> simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa mid) s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> gvs[] >>
  strip_tac >> first_x_assum ACCEPT_TAC
QED

Theorem loccode_copy_immutable_holds_run:
  compile_ensure_in_memory src LocCode sz wc cenv.ce_is_ctor
    cenv.ce_imm_alloca sa = (dst,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand sa region) /\
  0 < sz /\ sz < dimword (:256) /\ sz MOD 32 = 0 /\
  immutable_holds cenv cx ty raw held es s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      immutable_holds cenv cx ty raw held es t
Proof
  strip_tac >> drule_all loccode_copy_windows_run >> strip_tac >>
  qexists `t` >> simp[] >> irule immutable_holds_capacity_frame >>
  qexists `s` >> simp[] >> first_x_assum ACCEPT_TAC
QED
