(* Checked consumer-layout probes. Not a counterexample to the whole seam. *)
Theory bodyIntCallCapacityProbe
Ancestors
  compileVyper exprLowering compileEnv vyperValueOperation valueEncoding
  vyperTypeSystem
Libs
  monadsyntax

Theorem bytes_widening_parameter_probe:
  let pkg = package_internal_fn [] F (\s. 0) F 0
       (Pure,F,F,"f",[("x",BaseT (BytesT (Dynamic 65)))],[],NoneT,[]) in
    FST (SND (SND pkg)) = [("x",F)] /\
    FLOOKUP (FST (SND pkg)).ce_vars "x" = SOME (MemLoc 0 128) /\
    type_memory_bytes (FST (SND pkg)) (BaseT (BytesT (Dynamic 1))) = 64 /\
    type_memory_size (BaseTV (BytesT (Dynamic 1))) = 64 /\
    safe_cast (BaseTV (BytesT (Dynamic 65))) (BytesV [0w]) = SOME (BytesV [0w]) /\
    ~(128 <= MAX 32 (type_memory_bytes (FST (SND pkg))
                                    (BaseT (BytesT (Dynamic 1)))))
Proof
  EVAL_TAC >> simp[]
QED

Theorem bytes_widening_stage_probe:
  let sa = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
             cs_current_bb := "entry"; cs_current_insts := [];
             cs_blocks := []; cs_data_sections := []|> in
  let out = compile_stage_intcall_args ce
      [StackValue (BaseT (BytesT (Dynamic 1))) (Lit 256w)] [F]
      [BaseT (BytesT (Dynamic 1))] sa in
    MAP (\i. (i.inst_id,i.inst_operands))
      (FILTER (\i. i.inst_opcode = ALLOCA) (SND out).cs_current_insts) =
      [(0,[Lit 64w])]
Proof
  EVAL_TAC >> simp[]
QED

Theorem word_and_fixed_parameter_probe:
  let pkg = package_internal_fn [] F (\s. 0) F 0
       (Pure,F,F,"f",[("x",ArrayT (BaseT (UintT 256)) (Fixed 2))],[],NoneT,[]) in
    FST (SND (SND pkg)) = [("x",F)] /\
    FLOOKUP (FST (SND pkg)).ce_vars "x" = SOME (MemLoc 0 64) /\
    type_memory_bytes (FST (SND pkg)) (ArrayT (BaseT (UintT 256)) (Fixed 2)) = 64 /\
    type_memory_size (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) = 64 /\
    safe_cast (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
      (ArrayV (SArrayV [])) = SOME (ArrayV (SArrayV [])) /\
    compute_pass_via_stack [BaseT (UintT 256)] 6 = [F] /\
    type_memory_bytes (FST (SND pkg)) (BaseT (UintT 256)) = 32 /\
    safe_cast (BaseTV (UintT 256)) (IntV 1) = SOME (IntV 1)
Proof
  EVAL_TAC >> simp[]
QED

Theorem dynarray_widening_parameter_probe:
  let pkg = package_internal_fn [] F (\s. 0) F 0
       (Pure,F,F,"f",[("x",ArrayT (BaseT (UintT 256)) (Dynamic 3))],[],NoneT,[]) in
    FST (SND (SND pkg)) = [("x",F)] /\
    FLOOKUP (FST (SND pkg)).ce_vars "x" = SOME (MemLoc 0 128) /\
    type_memory_bytes (FST (SND pkg)) (ArrayT (BaseT (UintT 256)) (Dynamic 1)) = 64 /\
    type_memory_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) = 64 /\
    safe_cast (ArrayTV (BaseTV (UintT 256)) (Dynamic 3))
      (ArrayV (DynArrayV [IntV 1])) = SOME (ArrayV (DynArrayV [IntV 1])) /\
    ~(128 <= MAX 32 (type_memory_bytes (FST (SND pkg))
                        (ArrayT (BaseT (UintT 256)) (Dynamic 1))))
Proof
  EVAL_TAC >> simp[]
QED

(* The stack annotation is used by the typed aggregate copy, not by the
   unwrap. Distinct annotations must not be silently replaced by MCOPY. *)
Theorem stack_annotation_stage_probe:
  let sa = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
             cs_current_bb := "entry"; cs_current_insts := [];
             cs_blocks := []; cs_data_sections := []|> in
  let out = compile_stage_intcall_args ce
      [StackValue (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Lit 256w)] [F]
      [ArrayT (BaseT (UintT 256)) (Fixed 2)] sa in
    MAP (\i. (i.inst_id,i.inst_operands))
      (FILTER (\i. i.inst_opcode = ALLOCA) (SND out).cs_current_insts) =
      [(0,[Lit 64w])]
Proof
  simp[compile_stage_intcall_args_def, unwrap_value_def] >>
  EVAL_TAC >> simp[] >>
  IF_CASES_TAC >> EVAL_TAC >> simp[]
QED

(* Unlike assignment/return widening, internal-call operands must match the
   declared parameter types exactly. Thus the widening probes above are not
   admissible caller operands for the frozen seam. *)
Theorem intcall_well_typed_parameter_types:
  well_typed_expr env (Call ty (IntCall fid) es drv) /\
  FLOOKUP env.fn_sigs fid = SOME fsig ==>
  MAP expr_type es = TAKE (LENGTH es) fsig.param_types
Proof
  Cases_on `fid` >> simp[well_typed_expr_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem bytes_widening_type_probe:
  type_widens_to tenv (BaseT (BytesT (Dynamic 1)))
    (BaseT (BytesT (Dynamic 65))) /\
  (FLOOKUP env.fn_sigs (NONE,"f") = SOME fsig /\
   fsig.param_types = [BaseT (BytesT (Dynamic 65))] ==>
   ~well_typed_expr env
     (Call ty (IntCall (NONE,"f"))
       [Name (BaseT (BytesT (Dynamic 1))) "x"] NONE))
Proof
  conj_tac >- (EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  strip_tac >> strip_tac >>
  drule_all intcall_well_typed_parameter_types >>
  simp[vyperASTTheory.expr_type_def]
QED
