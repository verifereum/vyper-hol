(* Actual-site credit for one staging allocation; no interval-id charge. *)
Theory bodyIntCallReserveProbe
Ancestors
  bodyIntCallResource actualAllocExec exprLoweringProps compileEnv
  emitHelper venomInst venomState finite_map words list
  compileVyper intCallCallee moduleLowering exprLowering

Theorem pending_alloca_site_bound:
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id NOTIN FDOM s.vs_allocas ==>
  alloca_lit_size inst <= pending_alloca_size func s
Proof
  strip_tac >>
  `MEM (alloca_lit_size inst)
    (MAP alloca_lit_size (FILTER (\i. i.inst_opcode = ALLOCA /\
       i.inst_id NOTIN FDOM s.vs_allocas) (fn_insts func)))` by
    (simp[MEM_MAP, MEM_FILTER] >> qexists_tac `inst` >> simp[]) >>
  drule (iffLR MEM_SPLIT) >> strip_tac >>
  simp[pending_alloca_size_def, SUM_APPEND]
QED

Theorem alloc_buffer_call_reserve:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  n < dimword (:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  margin <= unit_alloca_frame ctx ==>
  s.vs_alloca_next + n + margin < dimword (:256)
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  drule pending_alloca_site_bound >>
  simp[mk_inst_def, alloca_lit_size_def] >> strip_tac >>
  `n <= pending_alloca_size func s` by metis_tac[] >>
  drule_all alloca_room_call_reserve >>
  simp[]
QED

(* Minimal callee packaging does not itself promise a 64-byte frame. *)
Theorem empty_callee_frame_probe:
  let pkg = package_internal_fn [] F (\s. 0) F 0
       (Pure,F,F,"f",[],[],NoneT,[]) in
    internal_stack_size (FST (SND pkg)) (FST (SND (SND pkg))) = 0 /\
    let sa = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
               cs_current_bb := "entry"; cs_current_insts := [];
               cs_blocks := []; cs_data_sections := []|> in
    let sb = SND (compile_internal_function (FST (SND pkg)) []
                      F F 0 F F F 0 [] NONE sa) in
      FILTER (\i. i.inst_opcode = ALLOCA) sb.cs_current_insts = []
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

(* A genuine nonword unwrap, with its one real fresh allocation. *)
Theorem storage_pair_unwrap_charge_probe:
  let sa = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
             cs_current_bb := "entry"; cs_current_insts := [];
             cs_blocks := []; cs_data_sections := []|> in
  let sb = SND (unwrap_value ce
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2))
      <|ptr_location := LocStorage; ptr_operand := Lit 0w;
        ptr_buf := NONE|>) sa) in
    MAP (\i. (i.inst_id,i.inst_operands))
      (FILTER (\i. i.inst_opcode = ALLOCA)
        (FLAT (MAP (\bb. bb.bb_instructions) sb.cs_blocks) ++ sb.cs_current_insts)) =
        [(0,[Lit 64w])] /\
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA)
        (FLAT (MAP (\bb. bb.bb_instructions) sb.cs_blocks) ++ sb.cs_current_insts))) = 64 /\
    64 < 32 * sb.cs_next_id
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem unit_alloca_site_bound:
  MEM func ctx.ctx_functions /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA ==>
  alloca_lit_size inst <= unit_alloca_frame ctx
Proof
  strip_tac >>
  `MEM (alloca_lit_size inst)
    (MAP alloca_lit_size (FILTER (\i. i.inst_opcode = ALLOCA)
      (FLAT (MAP fn_insts ctx.ctx_functions))))` by
    (simp[MEM_MAP, MEM_FILTER, MEM_FLAT] >>
     qexists_tac `inst` >> simp[] >>
     qexists_tac `fn_insts func` >> simp[MEM_MAP] >> metis_tac[]) >>
  drule (iffLR MEM_SPLIT) >> strip_tac >> simp[unit_alloca_frame_def, SUM_APPEND]
QED

(* A large enough actual staging ALLOCA itself justifies the extra margin:
   no lower bound on the callee's own frame is required. *)
Theorem alloc_buffer_site_margin:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  n < dimword (:256) /\ margin <= n /\ MEM func ctx.ctx_functions ==>
  margin <= unit_alloca_frame ctx
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  drule_at (Pat `MEM _ (fn_insts _)`) unit_alloca_site_bound >>
  simp[mk_inst_def, alloca_lit_size_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> decide_tac
QED
