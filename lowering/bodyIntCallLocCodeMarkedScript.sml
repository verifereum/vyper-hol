(* Compiler structure for the joint LocCode counted window witness. *)
Theory bodyIntCallLocCodeMarked
Ancestors
  bodyIntCallStraightWitness bodyIntCallWindowCodeCopy bodyIntCallFreshCodeCopy exprSimCopy
  loweringHalt exprLoweringProps fragExec list rich_list venomInst

Theorem loccode_copy_straight_shape:
  compile_ensure_in_memory src LocCode sz wc mode imm sa = (dst,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule loccode_copy_split >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  Cases_on `mode` >> gvs[]
  >- (drule code_ctor_copy_insts >> strip_tac >>
      gvs[same_blocks_def, emitted_insts_def, DROP_APPEND1,
          APPEND_ASSOC, venomInstTheory.mk_inst_def, EVERY_MEM,
          venomInstTheory.is_terminator_def] >>
      rpt strip_tac >> gvs[venomInstTheory.is_terminator_def] >>
      first_x_assum drule >>
      strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule code_copy_insts >> strip_tac >>
  gvs[same_blocks_def, emitted_insts_def, DROP_APPEND1,
      APPEND_ASSOC, venomInstTheory.mk_inst_def, EVERY_MEM,
      venomInstTheory.is_terminator_def] >>
      rpt strip_tac >> gvs[venomInstTheory.is_terminator_def] >>
      first_x_assum drule >>
      strip_tac >> gvs[venomInstTheory.is_terminator_def]
QED

(* One counted endpoint frames every initialized immutable window together. *)
Theorem loccode_copy_windows_marked:
  compile_ensure_in_memory src LocCode sz wc cenv.ce_is_ctor
    cenv.ce_imm_alloca sa = (dst,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand sa region) /\
  0 < sz /\ sz < dimword (:256) /\ sz MOD 32 = 0 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (memory ==> run_inst_seq_mem_ok (emitted_insts sa sb) s) ==>
  ?t. gas_marked_exec memory (ctx,func) (\e. (INL (),e))
        (es,s) [] (INL ()) es (OK t) /\
    (cenv.ce_is_ctor ==> !name off itv iv.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) name =
        SOME (itv,iv) ==>
      mem_bytes_at off (type_memory_size itv) t.vs_memory =
        mem_bytes_at off (type_memory_size itv) s.vs_memory)
Proof
  strip_tac >> drule loccode_copy_straight_shape >> strip_tac >>
  drule_all loccode_copy_windows_run >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (irule compiled_straight_marked_exec >>
      simp[] >> qexistsl [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
