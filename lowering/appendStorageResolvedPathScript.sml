(* Word Append execution from a resolved storage or transient pointer. *)
Theory appendStorageResolvedPath
Ancestors
  stmtSimAppendStorage stmtSimAppendStorageCompose varsExt freshWrites
  stateFrame compileEnv loweringPosts venomState venomInst venomExecSemantics
  exprLowering exprLoweringProps list finite_map words

Theorem append_storage_word_run_reserved:
  compile_dynarray_append ce bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME w /\
  cap < dimword (:256) /\ ~s.vs_call_ctx.cc_static ==>
  (cap <= w2n (if tr then tload slot s else sload slot s) ==>
    ?a t. run_inst_seq (emitted_insts sa sf) s = Abort a t) /\
  (!len. len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
    ?u. run_inst_seq (emitted_insts sa sf) s = OK u /\
      state_frame u = state_frame
        (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
         else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s)) /\
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==>
        lookup_var x u = SOME a))
Proof
  strip_tac >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot /\
   eval_operand vop (drop_fresh sa s) = SOME w` by
    (simp[eval_operand_drop_fresh] >> metis_tac[]) >>
  `tload slot (drop_fresh sa s) = tload slot s /\
   sload slot (drop_fresh sa s) = sload slot s /\
   ~(drop_fresh sa s).vs_call_ctx.cc_static` by
    simp[drop_fresh_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sf) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sf) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     gvs[EVERY_MEM]) >>
  conj_tac >- suspend "full" >> suspend "stored"
QED

Resume append_storage_word_run_reserved[full]:
  strip_tac >>
  `cap <= w2n (if tr then tload slot (drop_fresh sa s)
              else sload slot (drop_fresh sa s))` by simp[] >>
  drule_all compile_dynarray_append_word_abort >> strip_tac >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  simp[vars_ext_result_def] >> metis_tac[]
QED

Resume append_storage_word_run_reserved[stored]:
  rpt strip_tac >>
  `len = w2n (if tr then tload slot (drop_fresh sa s)
              else sload slot (drop_fresh sa s))` by simp[] >>
  drule_all compile_dynarray_append_word_run >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sf) s = OK u /\ vars_ext t u` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >>
     asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa sf) s` >>
     simp[vars_ext_result_def]) >>
  qexists_tac `u` >> asm_rewrite_tac [] >> conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      qpat_x_assum `state_frame u = _` (fn th => pure_once_rewrite_tac [th]) >>
      qpat_x_assum `state_frame t = _` (fn th => pure_once_rewrite_tac [th]) >>
      Cases_on `tr` >> asm_simp_tac bool_ss [] >>
      simp_tac (srw_ss()) [GSYM wordsTheory.word_add_n2w,
        wordsTheory.n2w_w2n, GSYM wordsTheory.WORD_ADD_ASSOC] >>
      simp_tac (srw_ss()) [drop_fresh_def, sstore_def, tstore_def,
        LET_THM, state_frame_def]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Finalise append_storage_word_run_reserved
