(* Memory safety of the complete EC arithmetic instruction suffix. *)
Theory bodyMemEcArithContinuation
Ancestors
  bodyMemEcArithAssemble bodyMemEcArithPrefix fragExecMem

Theorem ecmul_insts_mem_ok:
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;scalar] ==> not_fresh_at sf x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sf sb) s
Proof
  strip_tac >> drule_all ecmul_prefix_take_safe >> disch_tac >>
  drule_all ecmul_prefix_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sf sm) s` by
    (qpat_x_assum `run_inst_seq_mem_ok _ s` mp_tac >>
     simp[listTheory.TAKE_APPEND1] >>
     qpat_x_assum `LENGTH _ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (qpat_assum `_ sm = (res,sb)`
       (mp_then Any mp_tac ec_precompile_suffix_mem_ok) >>
     simp[wordsTheory.dimword_def]) >>
  qpat_x_assum `emitted_insts sf sb = _` (fn th => rewrite_tac[th]) >>
  irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[]
QED
