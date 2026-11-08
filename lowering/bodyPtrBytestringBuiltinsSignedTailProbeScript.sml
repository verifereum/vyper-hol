Theory bodyPtrBytestringBuiltinsSignedTailProbe
Ancestors
  bodyPtrBytestringBuiltinsSliceGuardFixture exprLowering compileEnv
  exprSimConvert representationCleanPtr valueEncodingProofs
  ptrDiscipline venomState words list finite_map bodyPtrDefs valueEncoding
  fragExec venomExecSemantics ptrSafeRun venomInst

(* Source abbreviations keep the selected nested conversion visible. *)
Definition signed_tail_def:
  signed_tail =
    TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
      [TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
        [Name (BaseT (BytesT (Dynamic 1))) "b"]]
End

Theorem signed_tail_typed:
  FLOOKUP env.var_types "b" = SOME (BaseT (BytesT (Dynamic 1))) ==>
  well_typed_expr env signed_tail
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem signed_tail_slice_typed:
  FLOOKUP env.var_types "b" = SOME (BaseT (BytesT (Dynamic 1))) ==>
  well_typed_expr env
    (Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
      [slice_guard_source; signed_tail;
       Literal (BaseT (UintT 256)) (IntL 1)])
Proof
  EVAL_TAC >> simp[dimword_def] >> strip_tac >>
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qexists_tac `Dynamic 24576` >> simp[]
QED

Theorem signed_tail_compile:
  FLOOKUP cenv.ce_vars "b" = SOME (PtrVar p 64) ==>
  lower_value compile_expr cenv ty signed_tail sa =
    (do x <- compile_type_convert p (ConvBytestringToInt T 256 1);
        compile_type_convert x (ConvIntToInt T 256 F 256)
     od) sa
Proof
  strip_tac >>
  simp[signed_tail_def, lower_value_def, compile_expr_def,
       compile_type_builtin_dispatch_component_eq, compile_type_builtin_dispatch_body_def,
       compile_name_vv_def, unwrap_value_def, contextTheory.mk_ptr_def,
       is_word_type_def, is_bytestring_type_def, lowered_value_type_def,
       vyperASTTheory.expr_type_def, mk_convert_op_def,
       as_stack_val_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[as_stack_val_def, unwrap_value_def, is_word_type_def] >>
  gvs[comp_return_def] >>
  Cases_on `compile_type_convert v (ConvIntToInt T 256 F 256) cs''` >>
  gvs[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

Theorem signed_empty_robust:
  mem_agree_outside {32} (REPLICATE 64 (0w:word8)) mem ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV []) 0 mem
Proof
  strip_tac >> simp[val_in_memory_def, mem_bytes_at_def] >>
  `mem_bytes_at 0 32 mem = mem_bytes_at 0 32 (REPLICATE 64 0w)` by
    (irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
     simp[mem_agree_outside_def] >>
     disch_then (qspec_then `x` mp_tac) >>
     `x <> 32` by decide_tac >> simp[] >>
     disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[EL_mem_bytes_at]) >>
  gvs[mem_word_at_def, mem_bytes_at_def] >> EVAL_TAC >> simp[]
QED

Theorem signed_loader_prefix:
  compile_type_convert p (ConvBytestringToInt T 256 1) sa = (op,sb) ==>
  ?len s1 dp s2 data s3 empty s4 nonempty s5 masked s6 sub s7 bits s8.
    emit_op MLOAD [p] sa = (len,s1) /\
    emit_op ADD [p; Lit 32w] s1 = (dp,s2) /\
    emit_op MLOAD [dp] s2 = (data,s3) /\
    emit_op ISZERO [len] s3 = (empty,s4) /\
    emit_op ISZERO [empty] s4 = (nonempty,s5) /\
    emit_op MUL [data; nonempty] s5 = (masked,s6) /\
    emit_op SUB [Lit 32w; len] s6 = (sub,s7) /\
    emit_op MUL [sub; Lit 8w] s7 = (bits,s8) /\
    emit_op SAR [bits; masked] s8 = (op,sb)
Proof
  simp[compile_type_convert_def, load_bytestring_as_word_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[comp_return_def]
QED

Theorem signed_mask_rejects_taint:
  inst.inst_opcode = MUL /\ inst.inst_operands = [data; mask] /\
  op_taint tn data <> {} ==> ~taint_ok fn tn inst s
Proof
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem signed_payload_load_taint:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [dp] /\
  inst.inst_outputs = [data] /\ eval_operand dp s = SOME 32w /\
  tn.t_mem = {32} ==>
  op_taint (step_taint inst s s' tn) (Var data) = {0}
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def,
       out_taint_def, mem_word_taint_def, pred_setTheory.EXTENSION] >>
  EVAL_TAC >> simp[dimword_def]
QED

Theorem signed_empty_local_ghost:
  (!name entry. lookup_scopes name es.scopes = SOME entry ==>
     name = "b" /\ entry.type = BaseTV (BytesT (Dynamic 1)) /\
     entry.value = BytesV []) /\
  cenv.ce_vars = FEMPTY |+ ("b", PtrVar (Var p) 64) /\
  cenv.ce_return_pc = NONE /\ lookup_var p s = SOME 0w /\
  s.vs_memory = REPLICATE 64 (0w:word8) /\
  FLOOKUP G p = SOME (0,64) /\ tn.t_var = FEMPTY /\
  tn.t_mem = {32} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} ==>
  ghost_inv NONE cenv cx es G tn s
Proof
  strip_tac >> simp[ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[FLOOKUP_UPDATE, ptr_covers_def, op_taint_def] >>
  rpt strip_tac >> gvs[] >> irule signed_empty_robust >> simp[]
QED

Theorem signed_iszero_preserves_data_taint:
  inst.inst_opcode = ISZERO /\ inst.inst_outputs = [out] /\ data <> out ==>
  op_taint (step_taint inst s s' tn) (Var data) = op_taint tn (Var data)
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem signed_loaded_mask_rejected:
  ld.inst_opcode = MLOAD /\ ld.inst_operands = [dp] /\
  ld.inst_outputs = [data] /\ eval_operand dp s = SOME 32w /\ tn.t_mem = {32} /\
  z1.inst_opcode = ISZERO /\ z1.inst_outputs = [empty] /\ data <> empty /\
  z2.inst_opcode = ISZERO /\ z2.inst_outputs = [mask] /\ data <> mask /\
  mask_inst.inst_opcode = MUL /\ mask_inst.inst_operands = [Var data; Var mask] ==>
  ~taint_ok fn
    (step_taint z2 s2 s3 (step_taint z1 s1 s2 (step_taint ld s s1 tn))) mask_inst s3
Proof
  strip_tac >> irule signed_mask_rejects_taint >> simp[] >>
  drule_all signed_payload_load_taint >>
  simp[signed_iszero_preserves_data_taint]
QED

(* Compiler-derived fixture, not a hand-selected unsafe instruction list. *)
Definition signed_probe_cs_def:
  signed_probe_cs = (ARB:compile_state) with
    <|cs_next_id := 0; cs_next_var := 0; cs_current_insts := []|>
End

Definition signed_probe_insts_def:
  signed_probe_insts = (SND
    (compile_type_convert (Var "b") (ConvBytestringToInt T 256 1)
      signed_probe_cs)).cs_current_insts
End

Theorem signed_probe_insts_prefix:
  TAKE 6 signed_probe_insts =
    [mk_inst 0 MLOAD [Var "b"] ["%0"];
     mk_inst 1 ADD [Var "b"; Lit 32w] ["%1"];
     mk_inst 2 MLOAD [Var "%1"] ["%2"];
     mk_inst 3 ISZERO [Var "%0"] ["%3"];
     mk_inst 4 ISZERO [Var "%3"] ["%4"];
     mk_inst 5 MUL [Var "%2"; Var "%4"] ["%5"]]
Proof
  EVAL_TAC
QED

(* Runtime abbreviation for the local loader probe only. *)
Definition signed_probe_state_def:
  signed_probe_state = (ARB:venom_state) with
    <|vs_vars := FEMPTY |+ ("b",0w); vs_memory := REPLICATE 64 0w;
      vs_allocas := FEMPTY |+ (99,(0,64)); vs_fmp := 64w;
      vs_halted := F|>
End

Theorem signed_probe_runtime_prefix:
  run_inst_seq (TAKE 5 signed_probe_insts) signed_probe_state =
    OK (signed_probe_state with vs_vars :=
      FEMPTY |+ ("b",0w) |+ ("%0",0w) |+ ("%1",32w) |+
        ("%2",0w) |+ ("%3",1w) |+ ("%4",0w))
Proof
  EVAL_TAC >> simp[dimword_def, WORD_ADD_0] >> EVAL_TAC >> simp[]
QED

(* Prefix states and ghost folding are executable fixture abbreviations;
   they link the check to the emitted prefix rather than detached operands. *)
Definition signed_probe_after_def:
  signed_probe_after n =
    case run_inst_seq (TAKE n signed_probe_insts) signed_probe_state of
      OK s => s | _ => signed_probe_state
End

Definition signed_probe_taint_def:
  signed_probe_taint = entry_taint with t_mem := {32}
End

Definition signed_probe_ghost_def:
  signed_probe_ghost fuel ctx PG =
    FOLDL (\gt j. ghost_step fuel ctx PG (FST gt) (SND gt)
      (EL j signed_probe_insts) (signed_probe_after j))
      (FEMPTY |+ ("b",(0,64)), signed_probe_taint) [0;1;2;3;4]
End

Theorem signed_probe_executed_mask_rejected:
  !fuel ctx PG fn.
  ~taint_ok fn (SND (signed_probe_ghost fuel ctx PG))
    (EL 5 signed_probe_insts) (signed_probe_after 5)
Proof
  rpt gen_tac >> EVAL_TAC >> simp[dimword_def, WORD_ADD_0] >>
  EVAL_TAC >> simp[dimword_def, WORD_ADD_0] >> EVAL_TAC >> simp[] >>
  qexists_tac `Var "%2"` >> simp[pred_setTheory.EXTENSION]
QED
