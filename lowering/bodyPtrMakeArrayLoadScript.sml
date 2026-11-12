(* Raw counted MLOAD; typed cleanliness is deliberately a separate obligation. *)
Theory bodyPtrMakeArrayLoad
Ancestors
  wordLoadStorePtr typedCopyPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs venomInst
  venomExecSemantics venomState context

Theorem mload_ptr_path:
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  eval_operand (Var src) s = SOME a ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (OK ((update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (OK ((update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MLOAD [Var src] [tmp]`,
                     `lo` |-> `0`,
                     `u` |-> `update_var tmp (mload (w2n (a:256 word)) s) s`]
                    straight_line_ptr_edge) >>
     gvs[] >> simp[mk_inst_def, is_terminator_def, ptr_inst_ok_mload,
                  step_inst_base_opcode_eqs, exec_read1_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem mload_ptr_old_coverage:
  tmp <> dst /\ ptr_covers G tn dst s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id MLOAD [src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    dst ((update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >>
  drule_all mload_preserves_ptr_covers >>
  simp[ptr_covers_def, lookup_var_def]
QED
