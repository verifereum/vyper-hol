(* Operational restore/allocation boundary. The runner is the physical FMP;
 * vs_fmp is an unchanged interpreter field after lowering. Semantic coverage
 * and nonwrapping ledger hypotheses remain explicit, as in fmpRestoreProps. *)
Theory fmpLowerRestoreExec
Ancestors
  fmpLowerExec fmpRestoreProps analysisSimDefs venomExecSemantics
  venomInst venomState fmpLedgerProps list words finite_map

Theorem fmp_emit_restore_single:
  fmp_emit_restores runner supply [target] = (code,supply') /\
  lookup_var target s = SOME value ==>
  run_insts fuel ctx code s = OK (update_var runner value s)
Proof
  simp[fmpLowerDefsTheory.fmp_emit_restores_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[run_insts_def, step_inst_non_invoke, mk_inst_def,
       step_inst_base_opcode_eqs, eval_operand_def]
QED

(* A fresh runner cannot change any source operand when a restore writes it. *)
Theorem eval_operand_restore:
  op <> Var runner ==>
  eval_operand op (update_var runner value s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Connect the semantic pop certificate to the actual generated ASSIGN.
 * Coverage premises are deliberately not consequences of plan acceptance. *)
Theorem fmp_emit_restore_contract:
  fmp_ledger_ok (fn_insts fn) env s top regions /\
  MAP (\r. r.fr_mark) regions = st.frs_stack /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  fmp_pop_target popped = SOME target /\
  ~MEM runner (MAP (\r. r.fr_mark) regions) /\
  fmp_base_covers env prov /\
  fmp_escape_covers (fn_insts fn) env escaped /\
  fmp_capture_covers fn live p st.frs_captures capProtect /\
  fmp_emit_restores runner supply [target] = (code,supply') ==>
  let ps = TAKE (LENGTH popped) regions in
  let ks = DROP (LENGTH popped) regions in
  let newtop = (LAST ps).fr_lo in
  let next = update_var runner (n2w newtop) s in
    run_insts fuel ctx code s = OK next /\
    fmp_ledger_ok (fn_insts fn) env next newtop ks /\
    lookup_var runner next = SOME (n2w newtop) /\
    next.vs_memory = s.vs_memory /\ next.vs_fmp = s.vs_fmp /\
    MAP (\r. r.fr_mark) ks = kept /\ newtop <= top /\
    EVERY (\r. ~fmp_protected prov
      (live_vars_at live (FST p) (SND p)) escaped capProtect r.fr_site) ps
Proof
  strip_tac >> drule_all fmp_restore_contract >>
  simp[LET_THM] >> strip_tac >>
  drule_all fmp_emit_restore_single >> strip_tac >>
  simp[LET_THM, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem dalloca_after_restore_exec:
  lookup_var target s = SOME value /\
  eval_operand size_op s = SOME sz /\ size_op <> Var runner /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] ==>
  run_insts fuel ctx
    [mk_inst ri ASSIGN [Var target] [runner];
     mk_inst ai ADD [size_op;Lit 31w] [plus31];
     mk_inst ni NOT [Lit 31w] [mask];
     mk_inst mi AND [Var plus31;Var mask] [aligned];
     mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] s =
  OK (update_var runner (value + n2w (ceil32 (w2n sz)))
       (update_var out value
         (update_var aligned (n2w (ceil32 (w2n sz)))
           (update_var mask (~31w)
             (update_var plus31 (sz + 31w) (update_var runner value s))))))
Proof
  strip_tac >>
  simp[Once run_insts_def, step_inst_non_invoke, mk_inst_def,
       step_inst_base_opcode_eqs, eval_operand_def] >>
  irule (REWRITE_RULE [mk_inst_def] dalloca_expansion_exec) >>
  simp[eval_operand_restore, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Updating the runner leaves memory and the interpreter FMP untouched, even
 * when its new value differs from vs_fmp. This is the relation needed between
 * consecutive lowered allocations; runner = vs_fmp is not an invariant. *)
Theorem dalloca_expansion_runner_frame:
  eval_operand size_op s = SOME sz /\ lookup_var runner s = SOME frontier /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  run_insts fuel ctx
    [mk_inst ai ADD [size_op;Lit 31w] [plus31];
     mk_inst ni NOT [Lit 31w] [mask];
     mk_inst mi AND [Var plus31;Var mask] [aligned];
     mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] s = OK low ==>
  lookup_var out low = SOME frontier /\
  lookup_var runner low = SOME (frontier + n2w (ceil32 (w2n sz))) /\
  (low with vs_vars := s.vs_vars) = s /\
  (!v. ~MEM v [plus31;mask;aligned;runner;out] ==>
       lookup_var v low = lookup_var v s)
Proof
  strip_tac >> drule_all dalloca_expansion_exec >> strip_tac >> gvs[] >>
  fs[ALL_DISTINCT] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* This is a nonwrapping concrete allocation claim, unlike the modular word
 * identity. Fresh temporaries preserve every retained allocation mark. *)
Theorem dalloca_expansion_ledger:
  fmp_ledger_ok insts env s lo regions /\
  eval_operand size_op s = SOME sz /\
  lookup_var runner s = SOME (n2w lo) /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  EVERY (\v. ~MEM v (MAP (\r. r.fr_mark) regions))
    [plus31;mask;aligned;runner;out] /\
  fmp_dalloca_query insts env out = SOME site /\
  hi = lo + ceil32 (w2n sz) /\ hi < dimword (:256) /\
  run_insts fuel ctx
    [mk_inst ai ADD [size_op;Lit 31w] [plus31];
     mk_inst ni NOT [Lit 31w] [mask];
     mk_inst mi AND [Var plus31;Var mask] [aligned];
     mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] s = OK low ==>
  fmp_ledger_ok insts env low hi
    (<| fr_mark := out; fr_site := site; fr_lo := lo; fr_hi := hi |> :: regions) /\
  lookup_var runner low = SOME (n2w hi) /\
  low.vs_memory = s.vs_memory /\ low.vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule_all dalloca_expansion_runner_frame >> strip_tac >>
  `fmp_ledger_ok insts env low lo regions` by
    (irule fmp_ledger_frame >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  simp[Once fmp_ledger_ok_def, word_add_n2w] >>
  qpat_x_assum `low with vs_vars := s.vs_vars = s`
    (mp_tac o AP_TERM ``\st:venom_state. (st.vs_memory,st.vs_fmp)``) >> simp[]
QED

val _ = List.app (fn (name,th) =>
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected dependency in " ^ name))
  (DB.thms "fmpLowerRestoreExec");
