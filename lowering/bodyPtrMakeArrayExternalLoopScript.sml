(* Counted steps for the storage/transient copy CFG, not fixed-run fragments. *)
Theory bodyPtrMakeArrayExternalLoop
Ancestors
  bodyPtrMakeArrayStorageRobust bodyPtrMakeArrayCopiedWord
  typedCopyLoopHeaderPtr fragGasSeqPtr fragGasPathPtr venomExecSemantics
  venomInst venomState context

Theorem copy_loop_mul_ptr_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MUL [left;right] [out]) (update_var out (a*b) s))
    (step_taint (mk_inst id MUL [left;right] [out]) s (update_var out (a*b) s) tn)
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MUL [left;right] [out]) s =
    OK (update_var out (a*b) s)` by
    (simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MUL [left;right] [out]) s` by
    (irule typed_copy_loop_test_check >> simp[update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MUL [left;right] [out]) (update_var out (a*b) s))
    (step_taint (mk_inst id MUL [left;right] [out]) s (update_var out (a*b) s) tn)
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MUL [left;right] [out]`,
                     `lo` |-> `0`,
                     `u` |-> `update_var out ((a:256 word)*b) s`]
                    straight_line_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED
