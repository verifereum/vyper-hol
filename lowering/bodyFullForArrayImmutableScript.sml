(* Constructor and runtime immutable element copying on one selected run. *)
Theory bodyFullForArrayImmutable
Ancestors
  bodyFullForArray bodyImmCopyMemory whitelistForIterImmCopy exprSimCopy
  exprLoweringProps fragGasOriginPtrLoop fragGasSeqPtr venomInst
  words arithmetic list

Theorem for_array_immutable_element_path_full:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + bytes < dimword (:256) /\
  (cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n b) bytes) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  code = emitted_insts sa sb /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n b + 32 * ((bytes + 31) DIV 32) <= s.vs_alloca_next /\
  (cenv.ce_is_ctor ==>
    w2n a + 32 * ((bytes + 31) DIV 32) <= s.vs_alloca_next /\
    w2n a + 32 * ((bytes + 31) DIV 32) < dimword (:256)) /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn code s Gf tf) ==>
  ?z. copy_runtime_frame sa s sb z /\
    val_wf tv v /\ val_in_memory tv v (w2n b) z.vs_memory /\
    val_footprint tv v <= bytes /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n b \/ w2n b + bytes <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tf))
Proof
  strip_tac >>
  `bytes <= 32 * ((bytes + 31) DIV 32)` by intLib.COOPER_TAC >>
  `w2n b + bytes <= s.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok code s` by
    (drule_all immutable_iter_copy_mem_ok >> simp[]) >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  drule immutable_iter_copy_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (gvs[emitted_insts_def] >>
     rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >>
     gvs[EVERY_MEM,FILTER_EQ_NIL] >>
     rpt conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq code s = OK z` by fs[copy_runtime_frame_def] >>
  qexists_tac `z` >> simp[] >> conj_tac >- gvs[] >> gen_tac >>
  qpat_assum `!H. inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` assume_tac) >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED
