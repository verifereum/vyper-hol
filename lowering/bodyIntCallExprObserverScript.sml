Theory bodyIntCallExprObserver
Ancestors
  abiEncoderObserver bodyIntCallObserverFrame fragExec compileEnv exprLowering vyperAST emitHelper
  venomInst venomState venomExecSemantics venomExecProofs venomInstProofs venomWf list rich_list pred_set

(* One package definition keeps completed-block ordering and the appended
   STOP identical in all containment, lookup and later region certificates.
   Unrelated function metadata is retained from a supplied template. *)
Definition expr_stop_function_def:
  expr_stop_function sa sb id template = template with fn_blocks :=
    <| bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []] |> ::
    emitted_blocks sa sb
End

Theorem expr_stop_function_lookup:
  lookup_block sb.cs_current_bb (expr_stop_function sa sb id template).fn_blocks =
    SOME <| bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []] |>
Proof
  simp[expr_stop_function_def, lookup_block_def, FIND_thm]
QED

Theorem expr_stop_function_stop:
  ?bb. lookup_block sb.cs_current_bb (expr_stop_function sa sb id template).fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sb.cs_current_insts) = SOME (mk_inst id STOP [] [])
Proof
  simp[expr_stop_function_lookup, get_instruction_def, EL_APPEND_EQN]
QED

Theorem expr_stop_function_has_code:
  ALL_DISTINCT (sb.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) ==>
  fn_has_code sa sb (expr_stop_function sa sb id template)
Proof
  strip_tac >> rw[fn_has_code_def]
  >- (irule MEM_lookup_block >>
      simp[expr_stop_function_def]) >>
  simp[expr_stop_function_lookup, IS_PREFIX_APPEND]
QED

Theorem expr_stop_function_empty:
  fn_has_code sa sa (expr_stop_function sa sa id template)
Proof
  irule expr_stop_function_has_code >> simp[emitted_blocks_def]
QED

Theorem expr_stop_function_same_block:
  sa.cs_current_bb = sb.cs_current_bb /\ emitted_blocks sa sb = [] ==>
  fn_has_code sa sb (expr_stop_function sa sb id template)
Proof
  strip_tac >> irule expr_stop_function_has_code >> simp[]
QED

(* This certificate mentions only static instruction successors. Jump entry is
   after the target's PHIs, whereas a sequential edge retains the block. *)
Theorem syntactic_region_closed:
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    inst_wf inst /\
    (~is_terminator inst.inst_opcode ==> (lbl,SUC idx) IN R) /\
    (!dest target. is_terminator inst.inst_opcode /\
      MEM dest (get_successors inst) /\
      lookup_block dest fn.fn_blocks = SOME target ==>
      (dest,phi_prefix_length target.bb_instructions) IN R)) ==>
  observer_region_closed ctx fn cut R
Proof
  strip_tac >> rw[observer_region_closed_def, abi_observer_step_def] >>
  qpat_assum `!lbl idx bb inst. _` (drule_all_then strip_assume_tac)
  >- (drule_all step_preserves_control_flow >> strip_tac >> simp[]) >>
  `step_inst_base inst s = OK middle` by gvs[step_inst_non_invoke] >>
  drule_all step_inst_base_term_succs >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem expr_stop_function_region_safe:
  (!lbl idx bb inst.
    (lbl,idx) IN R /\
    (lbl,idx) <> (sb.cs_current_bb,LENGTH sb.cs_current_insts) /\
    lookup_block lbl (expr_stop_function sa sb id template).fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    inst.inst_opcode <> INVOKE /\
    (!s h. ~s.vs_halted ==> step_inst_base inst s <> Halt h) /\
    (!s middle. ~s.vs_halted /\ step_inst_base inst s = OK middle ==>
      ~middle.vs_halted)) ==>
  observer_region_safe (expr_stop_function sa sb id template)
    (sb.cs_current_bb,LENGTH sb.cs_current_insts) R
Proof
  strip_tac >> simp[observer_region_safe_def] >> conj_tac
  >- (simp[expr_stop_function_lookup, get_instruction_def, EL_APPEND_EQN] >>
      qexists_tac `id` >> simp[]) >>
  first_x_assum mp_tac >> simp[]
QED

(* The same syntactic opcode inventory can supply the frame premise without
   restricting any instruction in the old prefix or outside the region. *)
Theorem syntactic_region_readonly:
  EVERY readonly_opcode ops /\
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    MEM inst.inst_opcode ops) ==>
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    readonly_opcode inst.inst_opcode)
Proof
  simp[EVERY_MEM] >> metis_tac[]
QED

(* Concrete states share the block inventory across certificate outputs. *)
Definition ifexp_observer_start_def:
  ifexp_observer_start =
    <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 1;
      cs_current_bb := "entry";
      cs_current_insts := [mk_inst 0 SSTORE [Lit 0w; Lit 1w] []];
      cs_blocks := []; cs_data_sections := []|>
End

Definition ifexp_observer_end_def:
  ifexp_observer_end =
    <|cs_next_var := 1; cs_next_label := 3; cs_next_id := 6;
      cs_current_bb := "@exit_2"; cs_current_insts := [];
      cs_blocks :=
        [<|bb_label := "@else_1"; bb_instructions :=
           [mk_inst 4 ASSIGN [Lit 9w] ["%0"];
            mk_inst 5 JMP [Label "@exit_2"] []]|>;
         <|bb_label := "@then_0"; bb_instructions :=
           [mk_inst 2 ASSIGN [Lit 7w] ["%0"];
            mk_inst 3 JMP [Label "@exit_2"] []]|>;
         <|bb_label := "entry"; bb_instructions :=
           [mk_inst 0 SSTORE [Lit 0w; Lit 1w] [];
            mk_inst 1 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []]|>];
      cs_data_sections := []|>
End

Theorem ifexp_observer_compile_probe:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL T))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9))) ifexp_observer_start =
    (StackValue (BaseT (UintT 256)) (Var "%0"),ifexp_observer_end)
Proof
  simp[ifexp_observer_start_def, ifexp_observer_end_def,
       Once compile_expr_def, lower_value_def, expr_type_def,
       is_word_type_def, fresh_var_def, fresh_label_def, fresh_label_output_def,
       emit_inst_def, emit_def, fresh_id_def, new_block_def,
       compile_ifexp_arm_def] >>
  simp[compile_expr_def, compile_literal_vv_def, unwrap_value_def,
       is_word_type_def, expr_type_def, comp_return_def, comp_bind_def,
       fresh_id_def, emit_def] >> EVAL_TAC >> simp[]
QED

Definition ifexp_observer_region_def:
  ifexp_observer_region =
    {("entry",1); ("@then_0",0); ("@then_0",1);
     ("@else_1",0); ("@else_1",1); ("@exit_2",0)}
End

Theorem ifexp_observer_region_start:
  (ifexp_observer_start.cs_current_bb,
   LENGTH ifexp_observer_start.cs_current_insts) IN ifexp_observer_region /\
  (!i. i < LENGTH ifexp_observer_start.cs_current_insts ==>
    (ifexp_observer_start.cs_current_bb,i) NOTIN ifexp_observer_region)
Proof
  simp[ifexp_observer_start_def, ifexp_observer_region_def]
QED

Theorem ifexp_observer_has_code:
  fn_has_code ifexp_observer_start ifexp_observer_end
    (expr_stop_function ifexp_observer_start ifexp_observer_end id template)
Proof
  irule expr_stop_function_has_code >>
  EVAL_TAC
QED

Theorem ifexp_observer_stop:
  ?bb. lookup_block "@exit_2"
    (expr_stop_function ifexp_observer_start ifexp_observer_end id template).fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME (mk_inst id STOP [] [])
Proof
  mp_tac (Q.INST [`sa` |-> `ifexp_observer_start`,
                 `sb` |-> `ifexp_observer_end`] expr_stop_function_stop) >>
  simp[ifexp_observer_end_def]
QED

Theorem ifexp_observer_region_closed:
  observer_region_closed ctx
    (expr_stop_function ifexp_observer_start ifexp_observer_end id template)
    ("@exit_2",0) ifexp_observer_region
Proof
  irule syntactic_region_closed >>
  simp[ifexp_observer_region_def] >> rpt strip_tac >>
  gvs[expr_stop_function_def, ifexp_observer_start_def,
      ifexp_observer_end_def, emitted_blocks_def,
      lookup_block_def, FIND_thm, get_instruction_def] >>
  gvs[mk_inst_def, inst_wf_def, is_terminator_def, get_successors_def,
      get_label_def, phi_prefix_length_def, ifexp_observer_region_def]
QED

Theorem ifexp_observer_region_safe:
  observer_region_safe
    (expr_stop_function ifexp_observer_start ifexp_observer_end id template)
    ("@exit_2",0) ifexp_observer_region
Proof
  `observer_region_safe
    (expr_stop_function ifexp_observer_start ifexp_observer_end id template)
    (ifexp_observer_end.cs_current_bb,
     LENGTH ifexp_observer_end.cs_current_insts) ifexp_observer_region`
    suffices_by simp[ifexp_observer_end_def] >>
  irule expr_stop_function_region_safe >>
  simp[ifexp_observer_region_def, ifexp_observer_end_def] >> rpt strip_tac >>
  gvs[expr_stop_function_def, ifexp_observer_start_def,
      ifexp_observer_end_def, emitted_blocks_def,
      lookup_block_def, FIND_thm, get_instruction_def] >>
  gvs[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def,
       jump_to_def, update_var_def]
QED

Theorem ifexp_observer_region_readonly:
  (lbl,idx) IN ifexp_observer_region /\ (lbl,idx) <> ("@exit_2",0) /\
  lookup_block lbl
    (expr_stop_function ifexp_observer_start ifexp_observer_end id template).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  readonly_opcode inst.inst_opcode
Proof
  simp[ifexp_observer_region_def] >> rpt strip_tac >>
  gvs[expr_stop_function_def, ifexp_observer_start_def,
      ifexp_observer_end_def, emitted_blocks_def,
      lookup_block_def, FIND_thm, get_instruction_def] >>
  EVAL_TAC
QED

Theorem ifexp_observer_start_ok:
  compile_state_ok ifexp_observer_start
Proof
  simp[compile_state_ok_def, ifexp_observer_start_def,
       bound_labels_def, compiler_labels_future_def, DISJOINT_DEF,
       EXTENSION, fresh_label_output_def] >>
  EVAL_TAC
QED

(* Diagnostic variants only: alias the initial block and final empty cut.
   Shared concrete endpoints keep the lookup and compilation probes identical. *)
Definition ifexp_collision_start_def:
  ifexp_collision_start = ifexp_observer_start with cs_current_bb := "@exit_2"
End

Definition ifexp_collision_end_def:
  ifexp_collision_end = ifexp_observer_end with cs_blocks :=
    MAP (\bb. bb with bb_label :=
      if bb.bb_label = "entry" then "@exit_2" else bb.bb_label)
      ifexp_observer_end.cs_blocks
End

Theorem ifexp_collision_compile_probe:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL T))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9))) ifexp_collision_start =
    (StackValue (BaseT (UintT 256)) (Var "%0"),ifexp_collision_end)
Proof
  simp[ifexp_collision_start_def, ifexp_collision_end_def,
       ifexp_observer_start_def, ifexp_observer_end_def,
       Once compile_expr_def, lower_value_def, expr_type_def,
       is_word_type_def, fresh_var_def, fresh_label_def, fresh_label_output_def,
       emit_inst_def, emit_def, fresh_id_def, new_block_def,
       compile_ifexp_arm_def] >>
  simp[compile_expr_def, compile_literal_vv_def, unwrap_value_def,
       is_word_type_def, expr_type_def, comp_return_def, comp_bind_def,
       fresh_id_def, emit_def] >> EVAL_TAC >> simp[]
QED

Theorem ifexp_collision_has_code:
  fn_has_code ifexp_collision_start ifexp_collision_end
    (template with fn_blocks := emitted_blocks ifexp_collision_start ifexp_collision_end)
Proof
  simp[fn_has_code_def, ifexp_collision_start_def, ifexp_collision_end_def,
       ifexp_observer_start_def, ifexp_observer_end_def, emitted_blocks_def,
       lookup_block_def, FIND_thm] >> rpt strip_tac >> gvs[]
QED

Theorem ifexp_collision_ids_distinct:
  fn_inst_ids_distinct
    (template with fn_blocks := emitted_blocks ifexp_collision_start ifexp_collision_end)
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def, ifexp_collision_start_def,
       ifexp_collision_end_def, ifexp_observer_start_def,
       ifexp_observer_end_def, emitted_blocks_def, mk_inst_def]
QED

Theorem ifexp_collision_no_stop:
  fn_has_code ifexp_collision_start ifexp_collision_end fn ==>
  ~(?bb id. lookup_block ifexp_collision_end.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH ifexp_collision_end.cs_current_insts) =
      SOME (mk_inst id STOP [] []))
Proof
  simp[fn_has_code_def, ifexp_collision_start_def, ifexp_collision_end_def,
       ifexp_observer_start_def, ifexp_observer_end_def, emitted_blocks_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then
    `<|bb_label := "@exit_2"; bb_instructions :=
        [mk_inst 0 SSTORE [Lit 0w; Lit 1w] [];
         mk_inst 1 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []]|>` mp_tac) >>
  simp[] >> strip_tac >> gvs[get_instruction_def, mk_inst_def]
QED

Theorem ifexp_collision_stop_package_fails:
  ~fn_has_code ifexp_collision_start ifexp_collision_end
    (expr_stop_function ifexp_collision_start ifexp_collision_end id template)
Proof
  strip_tac >> drule ifexp_collision_no_stop >>
  metis_tac[expr_stop_function_stop]
QED
