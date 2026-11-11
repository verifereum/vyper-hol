(* Pointer safety of the computed SHA256 precompile call. *)
Theory bodyPtrHashBuiltinsShaCall
Ancestors bodyPtrHashBuiltinsBoundary ptrSafeRun ptrDiscipline
  exprSimHash fragGasSeqPtr venomState venomInst venomExecSemantics words
  finite_map pred_set contextCodegenRel codegenRel

Theorem hash_staticcall_inst_ok:
  !D ctx fn G tn s t id gas p len q out w n r b sz c cap.
    eval_operand gas s <> NONE /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    FLOOKUP G p = SOME (b,sz) /\ FLOOKUP G q = SOME (c,cap) /\
    b <= w2n w /\ w2n w + w2n n <= b+sz /\
    c <= w2n r /\ w2n r + 32 <= c+cap /\
    (!a. MEM a [gas;Lit 2w;Var p;len;Var q;Lit 32w] ==> op_taint tn a = {}) /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) s = OK t /\
    t.vs_requests = s.vs_requests ==>
    ptr_inst_ok D 0 0 ctx fn G tn
      (mk_inst id STATICCALL [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) s
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (32w:bytes32) = 32` by wordsLib.WORD_DECIDE_TAC >>
  simp[ptr_inst_ok_def, allocas_from_def, step_inst_non_invoke, mk_inst_def] >>
  conj_tac >-
    (simp[GSYM mk_inst_def] >> irule hash_staticcall_access >>
     simp[eval_operand_def] >> metis_tac[]) >>
  simp[GSYM mk_inst_def] >> irule hash_staticcall_taint >> metis_tac[]
QED

Theorem hash_staticcall_ghost:
  !PG G tn s t id gas p len q out a w n r.
    eval_operand gas s = SOME a /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp ==>
    step_prov PG G (mk_inst id STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) t = DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) s t tn =
      tn with <|t_var := tn.t_var |+ (out,{});
        t_mem := tn.t_mem DIFF
          range_bytes [(w2n r,MIN 32 (LENGTH t.vs_returndata))]|>
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (32w:bytes32) = 32` by wordsLib.WORD_DECIDE_TAC >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, taint_component_equality,
    hash_staticcall_mem_taint, source_memory_write_ranges_def,
    memory_range_of_operands_def, eval_operand_def]
QED


Theorem hash_sha256_call_success:
  !id gas p len q out s a w n r outcome rest bs.
    eval_operand gas s = SOME a /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    read_memory (w2n w) (w2n n) s = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
    ?t. step_inst_base (mk_inst id STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) s = OK t /\
      t.vs_requests = s.vs_requests /\ t.vs_allocas = s.vs_allocas /\
      t.vs_fmp = s.vs_fmp /\ LENGTH t.vs_returndata = 32 /\
      lookup_var out t = SOME 1w
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `update_var out 1w
    ((write_memory_with_expansion (w2n r)
      (word_to_bytes (SHA_256_bytes bs) T) s) with
        <|vs_returndata := word_to_bytes (SHA_256_bytes bs) T;
          vs_outcomes := rest|>)` >>
  conj_tac >- (irule step_STATICCALL_sha256 >> simp[] >> metis_tac[]) >>
  simp[update_var_def, write_memory_with_expansion_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem hash_sha256_call_failure:
  !id gas p len q out s a w n r.
    eval_operand gas s = SOME a /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
    ?t. step_inst_base (mk_inst id STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) s = OK t /\
      t.vs_requests = s.vs_requests /\ t.vs_allocas = s.vs_allocas /\
      t.vs_fmp = s.vs_fmp /\ t.vs_returndata = [] /\
      lookup_var out t = SOME 0w
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `update_var out 0w
    ((write_memory_with_expansion (w2n r) [] s) with
      <|vs_returndata := [];vs_outcomes := DROP 1 s.vs_outcomes|>)` >>
  conj_tac >- (irule step_STATICCALL_sha256_fail >> simp[] >> metis_tac[]) >>
  simp[update_var_def, write_memory_with_expansion_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem hash_staticcall_clean_output:
  !id gas p len q out s t tn a w n r.
    eval_operand gas s = SOME a /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\ LENGTH t.vs_returndata = 32 ==>
    !i. w2n r <= i /\ i < w2n r+32 ==>
      i NOTIN (step_taint (mk_inst id STATICCALL
        [gas;Lit 2w;Var p;len;Var q;Lit 32w] [out]) s t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (32w:bytes32) = 32` by wordsLib.WORD_DECIDE_TAC >>
  simp[step_taint_def] >> gen_tac >> strip_tac >>
  irule hash_staticcall_output_clean >>
  simp[source_memory_write_ranges_def, memory_range_of_operands_def,
    mk_inst_def, eval_operand_def]
QED
