(* Generated seven-instruction body adapter; the terminator is separate. *)
Theory exprPtrUnwrapGeneratedBody
Ancestors
  exprPtrUnwrapBodySegment copyExecution slotCopyExecution
  fragGasSeqPtr fragExec bodyPtrDefs ptrDiscipline venomState venomInst list

Theorem copy_generated_body_segment:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME srcword /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
  root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5 /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off + 32 <= capacity /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq (TAKE 7 (slot_copy_body_insts cs src (Var root) load)) s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      (TAKE 7 (slot_copy_body_insts cs src (Var root) load)) s Gf tnf /\
    t = update_var (slot_copy_var cs 0) (k+1w)
      (update_var (slot_copy_var cs 6) (k+1w)
        (mstore (w2n (a+n2w off)) (slot_copy_word load s (srcword+k))
          (update_var (slot_copy_var cs 5) (a+n2w off)
            (update_var (slot_copy_var cs 4) (n2w off)
              (update_var (slot_copy_var cs 3) (slot_copy_word load s (srcword+k))
                (update_var (slot_copy_var cs 2) (srcword+k) s)))))) /\
    op_taint tnf (Var (slot_copy_var cs 0)) = {} /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n (a+n2w off) <= j /\ j < w2n (a+n2w off) + 32}) UNION
      {w2n (a+n2w off) + j | j IN
        key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) (srcword+k)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
         p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
         p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
      p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
      p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 /\
      ptr_covers G tn p s c ==> ptr_covers Gf tnf p t c)
Proof
  strip_tac >>
  simp_tac (pure_ss ++ numSimps.REDUCE_ss)
    [slot_copy_body_insts_def, TAKE_def, COND_CLAUSES] >>
  irule copy_body_segment >>
  simp[slot_copy_var_distinct] >> qexists_tac `capacity` >> simp[]
QED
