Theory gasFocusPrefixDriver
Ancestors
  o1PipelineCorrect o1SafeUpto o1PassContract gasEvents
  codegenEntryRel asmFrameRel frameJointTrace asmSem symbolResolve
  frameOutcome callTrace vfmExecution list rich_list

(* Proof goals only. These ML values register no HOL definitions or theorems.
   The packet, CFG cursor and frame-plan conjuncts will be joined here once
   their main-based owner theories are available. *)

val focus_producer_goal : term = ``
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_run_state_ok vs0 /\ unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  initial_ctx_rel_tail [] cpl prog out.po_unit.cu_context vs0 es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  (!gs. ?D f extra.
    dead_wf D /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with vs_gas_readings := gs) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      markf gs ++ extra) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      !D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with vs_gas_readings := raw ++ [0w]))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with vs_gas_readings := raw ++ [0w]) vs0 /\
        o1_lowered_inv out.po_unit.cu_context vs0
``;

(* The actual execution component of the simultaneous motive. The empty
   tail belongs to the initial relation; the current tail is explicit. *)
val focus_execution_motive : term = ``
  \vs0 ctx prog data es0 ast0 result final tail q0 evs qs q n ast es.
    joint_trace vs0 ctx q0 evs qs q /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast0 = AsmOK ast /\
    asm_frame_rel_tail tail prog data es0 ast es /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final
``;

(* Every free name is intentional. A missing imported constant must fail
   this check rather than silently becoming a universally bound predicate. *)
val producer_parameters =
  ["rpolicy", "unit", "out", "vs0", "cpl", "prog", "es0", "nm",
   "entryfn", "lbl", "lo", "markf", "project", "result", "final"];

val _ =
  if type_of focus_producer_goal = type_of ``T`` andalso
     HOLset.equal
       (HOLset.fromList String.compare
          (map (fst o dest_var) (free_vars focus_producer_goal)),
        HOLset.fromList String.compare producer_parameters)
  then ()
  else raise Fail "focus producer goal has unexpected type or free names";

val _ =
  if null (free_vars focus_execution_motive) andalso
     type_of (snd (strip_abs focus_execution_motive)) = type_of ``T``
  then ()
  else raise Fail "focus execution motive is not a closed Boolean predicate";

val _ = app
  (fn (thy, name) =>
    if is_const (prim_mk_const {Thy = thy, Name = name}) then ()
    else raise Fail (thy ^ "$" ^ name ^ " is not a constant"))
  [("o1PipelineCorrect", "o1_pipeline"), ("o1SafeUpto", "o1_safe_upto"),
   ("gasEvents", "gas_events_blocks"),
   ("codegenEntryRel", "initial_ctx_rel_tail"),
   ("frameJointTrace", "joint_trace"),
   ("asmFrameRel", "asm_frame_rel_tail")];
