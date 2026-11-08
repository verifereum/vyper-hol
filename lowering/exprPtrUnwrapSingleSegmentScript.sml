(* Singleton aggregate slots retain the loaded key's dead-byte taint. *)
Theory exprPtrUnwrapSingleSegment
Ancestors
  exprPtrUnwrapLoadSegment exprPtrUnwrapStoreSegment exprPtrUnwrapCopyEdges
  exprPtrUnwrapFrames slotCopyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  instIdxIndep decoderGhostFramePtr exprLoweringProps codegenRel
  ghostPcTransportPtr instSeqComposePtr list


Theorem copy_store_cursor[local]:
  ptr_covers G tn root s 32 /\
  eval_operand (Var root) s = SOME addr /\ eval_operand v s = SOME value /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_seq_ptr D lo ctx fn PG G tn [mk_inst id MSTORE [Var root;v] []] s H tm ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id MSTORE [Var root;v] []]
    (s with vs_inst_idx := k) H tm
Proof
  strip_tac >> gen_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id MSTORE [Var root;v] [])
    (s with vs_inst_idx := k)` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[inst_seq_ptr_def, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
    copy_mstore_inst_idx]
QED

Theorem copy_single_slot_segment:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  op_taint tn src = {} /\ root <> out /\ ptr_covers G tn root s 32 /\
  lookup_var root s = SOME addr /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq
      [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []]
      s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []]
      s Gf tnf /\
    t = mstore (w2n addr) (slot_copy_word load s key)
      (update_var out (slot_copy_word load s key) s) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
        {w2n addr+k | k IN key_taint
          (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x k. x <> out /\ ptr_covers G tn x s k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all copy_slot_load_segment >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s H tm` >>
  rename1 `u = update_var out (slot_copy_word load s key) s` >>
  `ptr_covers H tm root u 32` by metis_tac[] >>
  `eval_operand (Var root) u = SOME addr /\
   eval_operand (Var out) u = SOME (slot_copy_word load s key)` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  drule_all copy_store_segment >>
  disch_then (qspecl_then [`id+1`, `fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`, `t`] >>
  conj_tac
  >- (qpat_assum `run_inst_seq [mk_inst id load [src] [out]] s = OK u`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `[mk_inst (id+1) MSTORE [Var root;Var out] []]` mp_tac) >>
      simp[]) >>
  conj_tac
  >- (irule (SRULE [] (Q.SPEC `[mk_inst id load [src] [out]]` inst_seq_ptr_append)) >>
      conj_tac >- (gvs[is_terminator_def]) >>
      qexistsl [`H`, `u`, `tm`] >> asm_rewrite_tac[] >>
      irule copy_store_cursor >> asm_rewrite_tac[] >> metis_tac[]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
