Theory bodyPtrTypeBuiltinsWidenActual
Ancestors
  bodyPtrTypeBuiltinsWidenSemantic assignBasePtrWidenEndpoint
  bodyPtrDefs exprLoweringProps exprLowering compileEnv venomState

(* The sequence-existence boundary supplies the run required by the counted
   certificate. No erased semantic path is used as pointer-safety evidence. *)
Theorem widen_copy_actual_counted_certificate:
  compile_bytestring_widen_copy capacity (Var src) n sa = (op,sb) /\
  fn_has_code sa sb fn /\ 0 < n /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\ n <= capacity /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  expr_val_at cenv cx tsrc slo sa es v (Var src) s0 /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ ~is_word_type tsrc /\
  val_wf tv v /\ val_footprint tv v <= n /\ lookup_var src s0 = SOME a /\
  ptr_covers G0 tn0 src s0 n /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
  ~s0.vs_halted /\ lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions) /\
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\ value_has_type tv v /\
  convert_result cx tsrc tdst v = INL vout ==>
  ?t dst b H th. run_inst_seq (emitted_insts sa sb) s0 = OK t /\ op = Var dst /\
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 H th
      (OK (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    lookup_var dst (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) = SOME b /\
    ptr_covers H th dst (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) capacity /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es sa G0 tn0 s0 H th /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv2 vout (w2n b) m)
Proof
  strip_tac >>
  `?q w. run_inst_seq (emitted_insts sa sb) s0 = OK q /\
    eval_operand op q = SOME w /\
    FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,capacity) /\
    w2n w + capacity < dimword(:256)` by
    (irule assign_base_widen_sequence_bound >> simp[] >> conj_tac
     >- (qexistsl_tac [`n`,`a`,`Var src`] >> simp[eval_operand_def]) >>
     metis_tac[]) >>
  drule_all widen_copy_converted_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`q`,`dst`,`b`,`G`,`th`] >> simp[]
QED
