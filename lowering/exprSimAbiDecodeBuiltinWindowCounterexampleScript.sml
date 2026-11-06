Theory exprSimAbiDecodeBuiltinWindowCounterexample
Ancestors
  exprSimAbiDecodeBuiltinWindowProbe exprSimAbiDecodeBuiltin
  context venomExecSemantics venomState venomInst finite_map relation
  fragExec emitHelperProps rich_list
Libs
  wordsLib

Definition window_ce_def:
  window_ce = (ARB:compile_env) with ce_struct_fields := FEMPTY
End

Definition window_start_def:
  window_start = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition window_lower_def:
  window_lower = lower_abi_decode (Lit 256w)
    (type_to_abi_dec_info window_ce.ce_struct_fields window_ce window_probe_type)
    (abi_static_size window_ce.ce_struct_fields window_probe_type)
    (abi_size_bound window_ce.ce_struct_fields window_probe_type)
    (type_memory_bytes window_ce window_probe_type) window_start
End

Definition window_fn_def:
  window_fn = mk_raw_function "window_probe"
    [<| bb_label := "entry";
        bb_instructions := (SND window_lower).cs_current_insts ++
          [mk_inst (SND window_lower).cs_next_id STOP [] []] |>]
End

Definition window_ctx_def:
  window_ctx = (ARB:venom_context) with ctx_functions := [window_fn]
End

Definition window_initial_def:
  window_initial = mstore 256 64w
    ((init_venom_state "entry") with vs_alloca_next := 1024)
End

Theorem window_code_shape:
  (SND window_lower).cs_blocks = [] /\
  (SND window_lower).cs_current_bb = "entry" /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (SND window_lower).cs_current_insts
Proof
  EVAL_TAC
QED

Theorem window_static_premises:
  abi_decoder_coherent window_ce FEMPTY window_ce.ce_struct_fields
    window_probe_type window_probe_tv /\
  assignable_type FEMPTY window_probe_type /\
  abi_decode_bytes_widths FEMPTY window_probe_type /\
  abi_decoder_operand_live window_start.cs_next_var (Lit 256w) /\
  fn_has_code window_start (SND window_lower) window_fn /\
  fn_inst_ids_distinct window_fn /\
  window_start.cs_blocks = (SND window_lower).cs_blocks /\
  ~window_initial.vs_halted /\
  window_initial.vs_current_bb = window_start.cs_current_bb /\
  window_initial.vs_inst_idx = LENGTH window_start.cs_current_insts /\
  fresh_vars_wrt (SND window_lower) window_initial
Proof
  simp_tac bool_ss [window_ce_def, combinTheory.K_THM] >>
  conj_tac >- (simp[] >> irule window_probe_coherent >> simp[]) >>
  simp_tac bool_ss [window_probe_typing] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >-
    (simp[fn_has_code_def, emitted_blocks_def, window_start_def,
      window_code_shape, window_fn_def, mk_raw_function_def,
      lookup_block_def, listTheory.FIND_thm] >> metis_tac[IS_PREFIX_APPEND]) >>
  conj_tac >- EVAL_TAC >>
  simp[window_start_def, window_code_shape] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  simp[compileEnvTheory.fresh_vars_wrt_def, window_initial_def,
    venomStateTheory.init_venom_state_def, venomStateTheory.mstore_def]
QED

Theorem window_input:
  eval_operand (Lit 256w) window_initial = SOME (n2w 256) /\
  val_in_memory (BaseTV (BytesT (Dynamic 64)))
    (BytesV (REPLICATE 64 (0w:word8))) 256 window_initial.vs_memory
Proof
  EVAL_TAC
QED

Theorem window_no_invoke:
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts window_fn)
Proof
  EVAL_TAC
QED

Theorem window_no_calls:
  !a b. ~fn_directly_calls window_ctx a b
Proof
  simp[fcgDefsTheory.fn_directly_calls_def, window_ctx_def,
    lookup_function_def, listTheory.FIND_thm, window_fn_def,
    mk_raw_function_def] >> rpt strip_tac >> gvs[] >>
  mp_tac window_no_invoke >> simp[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, window_fn_def,
    mk_raw_function_def] >> metis_tac[]
QED

Theorem window_no_tc_calls:
  !a b. ~TC (fn_directly_calls window_ctx) a b
Proof
  simp[Once relationTheory.TC_CASES1, window_no_calls]
QED

Theorem window_resources:
  abi_builtin_decode_site_resources window_ctx window_fn window_start
    (SND window_lower).cs_next_id
    (abi_static_size window_ce.ce_struct_fields window_probe_type)
    (abi_size_bound window_ce.ce_struct_fields window_probe_type)
    (type_memory_bytes window_ce window_probe_type) 64 256 1024 window_initial
Proof
  simp[abi_builtin_decode_site_resources_def,
    actualDecoderSitesTheory.decode_site_resources_def,
    exprLoweringPropsTheory.alloca_room_def, exprLoweringPropsTheory.fmp_room_def,
    window_no_tc_calls, window_static_premises,
    window_initial_def, init_venom_state_def, mstore_def] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem window_all_premises:
  lower_abi_decode (Lit 256w)
    (type_to_abi_dec_info window_ce.ce_struct_fields window_ce window_probe_type)
    (abi_static_size window_ce.ce_struct_fields window_probe_type)
    (abi_size_bound window_ce.ce_struct_fields window_probe_type)
    (type_memory_bytes window_ce window_probe_type) window_start = window_lower /\
  abi_decoder_coherent window_ce FEMPTY window_ce.ce_struct_fields
    window_probe_type window_probe_tv /\
  assignable_type FEMPTY window_probe_type /\
  abi_decode_bytes_widths FEMPTY window_probe_type /\
  abi_decoder_operand_live window_start.cs_next_var (Lit 256w) /\
  (SND window_lower).cs_next_var <= (SND window_lower).cs_next_var /\
  eval_operand (Lit 256w) window_initial = SOME (n2w 256) /\
  val_in_memory (BaseTV (BytesT (Dynamic 64)))
    (BytesV (REPLICATE 64 (0w:word8))) 256 window_initial.vs_memory /\
  abi_builtin_decode_site_resources window_ctx window_fn window_start
    (SND window_lower).cs_next_id
    (abi_static_size window_ce.ce_struct_fields window_probe_type)
    (abi_size_bound window_ce.ce_struct_fields window_probe_type)
    (type_memory_bytes window_ce window_probe_type) 64 256 1024 window_initial /\
  fresh_vars_wrt (SND window_lower) window_initial /\
  fn_has_code window_start (SND window_lower) window_fn /\
  fn_inst_ids_distinct window_fn /\
  (!i. MEM i (fn_insts window_fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts window_fn)) /\
  (window_start.cs_blocks = (SND window_lower).cs_blocks \/
   (SND window_lower).cs_current_insts <> [] \/
   !bb. lookup_block (SND window_lower).cs_current_bb window_fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~window_initial.vs_halted /\
  window_initial.vs_current_bb = window_start.cs_current_bb /\
  window_initial.vs_inst_idx = LENGTH window_start.cs_current_insts
Proof
  simp[window_static_premises, window_input, window_resources,
    GSYM window_lower_def]
QED

Theorem window_block_halts:
  !fuel. ?s. exec_block fuel window_ctx (HD window_fn.fn_blocks) window_initial = Halt s
Proof
  gen_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``]) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 10 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  ntac 3 (pure_once_rewrite_tac [exec_block_def] >>
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``window_ctx``])) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Theorem window_run_halts:
  !fuel. ?s. run_from fuel window_ctx window_fn window_initial = Halt s
Proof
  gen_tac >> qspec_then `fuel` strip_assume_tac window_block_halts >>
  gvs[run_from_def, window_fn_def, mk_raw_function_def,
    lookup_block_def, listTheory.FIND_thm, window_initial_def,
    init_venom_state_def, mstore_def]
QED

Theorem window_run_never_reverts:
  !fuel u. run_from fuel window_ctx window_fn window_initial <> Abort Revert_abort u
Proof
  rpt gen_tac >> qspec_then `fuel` strip_assume_tac window_run_halts >> simp[]
QED

(* A concrete instance of every antecedent of the frozen theorem, followed
   by the negation of its entire success-or-revert conclusion.  The admitted
   lower_abi_decode_outcome theorem is not used in this certificate. *)
Theorem window_outcome_counterexample:
  (lower_abi_decode (Lit 256w)
    (type_to_abi_dec_info window_ce.ce_struct_fields window_ce window_probe_type)
    (abi_static_size window_ce.ce_struct_fields window_probe_type)
    (abi_size_bound window_ce.ce_struct_fields window_probe_type)
    (type_memory_bytes window_ce window_probe_type) window_start =
      (FST window_lower, SND window_lower) /\
  abi_decoder_coherent window_ce FEMPTY window_ce.ce_struct_fields
    window_probe_type window_probe_tv /\
  assignable_type FEMPTY window_probe_type /\
  abi_decode_bytes_widths FEMPTY window_probe_type /\
  abi_decoder_operand_live window_start.cs_next_var (Lit 256w) /\
  (SND window_lower).cs_next_var <= (SND window_lower).cs_next_var /\
  eval_operand (Lit 256w) window_initial = SOME (n2w 256) /\
  val_in_memory (BaseTV (BytesT (Dynamic 64)))
    (BytesV (REPLICATE 64 (0w:word8))) 256 window_initial.vs_memory /\
  abi_builtin_decode_site_resources window_ctx window_fn window_start
    (SND window_lower).cs_next_id
    (abi_static_size window_ce.ce_struct_fields window_probe_type)
    (abi_size_bound window_ce.ce_struct_fields window_probe_type)
    (type_memory_bytes window_ce window_probe_type)
    (LENGTH (REPLICATE 64 (0w:word8))) 256 1024 window_initial /\
  fresh_vars_wrt (SND window_lower) window_initial /\
  fn_has_code window_start (SND window_lower) window_fn /\
  fn_inst_ids_distinct window_fn /\
  (!i. MEM i (fn_insts window_fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts window_fn)) /\
  (window_start.cs_blocks = (SND window_lower).cs_blocks \/
   (SND window_lower).cs_current_insts <> [] \/
   !bb. lookup_block (SND window_lower).cs_current_bb window_fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~window_initial.vs_halted /\
  window_initial.vs_current_bb = window_start.cs_current_bb /\
  window_initial.vs_inst_idx = LENGTH window_start.cs_current_insts) /\
  ~((?t v. evaluate_abi_decode FEMPTY window_probe_type
                (REPLICATE 64 (0w:word8)) = INL v /\
       eval_operand (FST window_lower) t = SOME (n2w 1024) /\
       val_in_memory window_probe_tv v 1024 t.vs_memory /\
       fresh_vars_wrt (SND window_lower) t /\
       decode_site_effect window_ctx window_fn window_start.cs_next_var
         ({a | 1024 <= a /\ a < 1024 + type_memory_bytes window_ce window_probe_type} UNION
          {a | window_initial.vs_alloca_next <= a} UNION
          {a | ?id b sz. window_start.cs_next_id <= id /\
                 id < (SND window_lower).cs_next_id /\
                 FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz})
         window_initial t /\
       (!id. id < window_start.cs_next_id \/ (SND window_lower).cs_next_id <= id ==>
             FLOOKUP t.vs_allocas id = FLOOKUP window_initial.vs_allocas id) /\
       ~t.vs_halted /\ t.vs_current_bb = (SND window_lower).cs_current_bb /\
       t.vs_inst_idx = LENGTH (SND window_lower).cs_current_insts /\
       !fuel r. run_from fuel window_ctx window_fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' window_ctx window_fn window_initial = r) \/
    (?fuel r e u. run_from fuel window_ctx window_fn window_initial = r /\ exit_result r /\
       r = Abort Revert_abort u /\
       evaluate_abi_decode FEMPTY window_probe_type (REPLICATE 64 (0w:word8)) = INR e))
Proof
  conj_tac
  >- simp[window_static_premises, window_input, window_resources,
       GSYM window_lower_def] >>
  simp[window_probe_source, window_run_never_reverts]
QED

(* Audit the certificate itself, not the admitted outcome in its parent theory. *)
val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then
      print ("Checked oracle-free counterexample fact: " ^ name ^ "\n")
    else raise Fail ("non-clean window counterexample: " ^ name)
  end)
  [("window_outcome_counterexample", window_outcome_counterexample),
   ("window_run_halts", window_run_halts),
   ("window_probe_source", window_probe_source)];
