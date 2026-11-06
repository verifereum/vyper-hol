(* Outcome-exclusion probes for the padding witness. *)
Theory bodyPtrTypeBuiltinsPaddingOutcome
Ancestors
  bodyPtrTypeBuiltinsPaddingFrame bodyPtrTypeBuiltinsPaddingTarget
  bodyPtrTypeBuiltinsPaddingWitness
  gasExemptCert vyperState vyperInterpreter words fragGasPathPtr
  venomExecSemantics venomExecProofs ptrSafeRun ptrDiscipline venomState
  venomInst finite_map list

Theorem padding_source_returns:
  bind (eval_expr padding_actual_context padding_expr)
    (read_result padding_actual_context) (padding_source with gas_obs := gs) =
  (INL (IntV 0), padding_source with gas_obs := gs)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> simp[] >> EVAL_TAC
QED

Theorem padding_no_exempt_cert:
  ~gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr padding_actual_context padding_expr)
                  (read_result padding_actual_context)) (return ()))
    (padding_source,s) marks (err,ee) (leaf,final_s)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  simp[ignore_bind_def, bind_def, padding_source_returns, return_def]
QED

Theorem padding_straight_edge_inversion:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK u /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r ==>
  r = OK (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  G' = step_prov PG G i u /\ tn' = step_taint i s u tn
Proof
  strip_tac >>
  fs[gas_path_ptr_edge_def] >> gvs[step_inst_non_invoke] >>
  gvs[Once ghost_step_def, step_inst_non_invoke, fragExecTheory.exit_result_def]
QED

Theorem padding_path_first_edge:
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
  (r = OK s /\ G' = G /\ tn' = tn) \/
  (?k H tt u m.
    gas_path_ptr_edge D lo ctx fn PG G tn s k H tt (OK u) /\
    gas_path_ptr D lo ctx fn PG H tt u m G' tn' r) \/
  (?k. gas_path_ptr_edge D lo ctx fn PG G tn s k G' tn' r /\
       exit_result r)
Proof
  simp[Once gas_path_ptr_cases] >> metis_tac[]
QED

Theorem padding_path_blocked:
  (!n H tt r. ~gas_path_ptr_edge D lo ctx fn PG G tn s n H tt r) ==>
  !n G' tn' r. gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    r = OK s
Proof
  rpt strip_tac >> drule padding_path_first_edge >> metis_tac[]
QED

Theorem padding_path_one_prefix:
  (!n H tt r. gas_path_ptr_edge D lo ctx fn PG G tn s n H tt r ==>
      r = OK u /\ H = Gu /\ tt = tu) /\
  (!n H tt r. gas_path_ptr D lo ctx fn PG Gu tu u n H tt r ==> P r) ==>
  !n H tt r. gas_path_ptr D lo ctx fn PG G tn s n H tt r ==>
    r = OK s \/ P r
Proof
  rpt strip_tac >> drule padding_path_first_edge >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  gvs[fragExecTheory.exit_result_def] >> metis_tac[]
QED

(* Bounded concrete certificate abbreviation, not an alternative execution
   relation. The fallback branches are unused by the five checked steps. *)
Definition padding_prefix_def:
  (padding_prefix 0 =
    (padding_actual_machine, entry_taint with t_mem := {63})) /\
  (padding_prefix (SUC k) =
    if k < 5 then
      case padding_prefix k of (s,tn) =>
      case EL (k+3) (fn_insts padding_runtime_function) of i =>
      case step_inst_base i s of
        OK u => (u with vs_inst_idx := SUC s.vs_inst_idx,
                 step_taint i s u tn)
      | _ => (s,tn)
    else padding_prefix k)
End

Definition padding_prefix_machine_def:
  padding_prefix_machine k = FST (padding_prefix k)
End

Definition padding_prefix_taint_def:
  padding_prefix_taint k = SND (padding_prefix k)
End

Theorem padding_prefix_small:
  (!k. k < 5 ==>
    padding_prefix (k+1) =
      case padding_prefix k of (s,tn) =>
      case EL (k+3) (fn_insts padding_runtime_function) of i =>
      case step_inst_base i s of
        OK u => (u with vs_inst_idx := SUC s.vs_inst_idx,
                 step_taint i s u tn)
      | _ => (s,tn))
Proof
  gen_tac >> strip_tac >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD1, padding_prefix_def] >> simp[]
QED

