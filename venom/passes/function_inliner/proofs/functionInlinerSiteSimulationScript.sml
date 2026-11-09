(* Actual execution transport for one retained-callee site replacement. *)
Theory functionInlinerSiteSimulation
Ancestors
  functionInlinerSimulation functionInlinerContextTransport ctxLookupAgreeHelpers
  venomExecSemantics venomExecProofs venomInst functionInlinerDefs callLayoutDefs words list

Definition inline_lower_instruction_def:
  inline_lower_instruction ctx0 C n rank bound i <=>
    ?h. MEM h C.ctx_functions /\ qualified_origin ctx0 n h /\
        fcg_is_reachable (fcg_analyze ctx0) h.fn_name /\
        (rank : string -> num) h.fn_name < bound /\ MEM i (fn_insts h)
End

Theorem inline_lower_instruction_closed[local]:
  inliner_input_ok ctx0 /\
  (!h. MEM h C.ctx_functions ==> qualified_origin ctx0 n h) /\
  (!a b. MEM b (fcg_get_callees (fcg_analyze ctx0) a) ==>
    (rank : string -> num) b < rank a) /\
  lookup_function caller.fn_name C.ctx_functions = SOME caller /\
  final.fn_name = caller.fn_name ==>
  !i nm ops.
    inline_lower_instruction ctx0 C n rank (rank caller.fn_name) i /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) ==>
    lookup_function nm C.ctx_functions =
      lookup_function nm (site_replace C caller final).ctx_functions /\
    (!h. lookup_function nm C.ctx_functions = SOME h ==>
      EVERY (inline_lower_instruction ctx0 C n rank (rank caller.fn_name))
        (fn_insts h))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  fs[inline_lower_instruction_def] >>
  `i.inst_operands = Label nm::ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `rank nm < rank h.fn_name` by
    metis_tac[qualified_origin_retained_call_rank] >>
  `fcg_is_reachable (fcg_analyze ctx0) nm` by
    metis_tac[qualified_origin_retained_call_reachable] >>
  `nm <> caller.fn_name` by (strip_tac >> gvs[]) >>
  conj_tac
  >- (drule_all site_replace_lookup >> simp[]) >>
  rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule (iffRL inline_lower_instruction_def) >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  qexists `callee` >>
  `MEM callee C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `callee.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  simp[]
QED

Theorem inline_lower_run_context:
  inliner_input_ok ctx0 /\
  (!h. MEM h C.ctx_functions ==> qualified_origin ctx0 n h) /\
  (!a b. MEM b (fcg_get_callees (fcg_analyze ctx0) a) ==>
    (rank : string -> num) b < rank a) /\
  lookup_function caller.fn_name C.ctx_functions = SOME caller /\
  final.fn_name = caller.fn_name /\
  MEM fn C.ctx_functions /\
  fcg_is_reachable (fcg_analyze ctx0) fn.fn_name /\
  rank fn.fn_name < rank caller.fn_name ==>
  run_blocks fuel C fn s = run_blocks fuel (site_replace C caller final) fn s
Proof
  strip_tac >> irule (cj 3 run_defs_predicate_cong) >>
  qexists `inline_lower_instruction ctx0 C n rank (rank caller.fn_name)` >>
  conj_tac
  >- (metis_tac[inline_lower_instruction_closed]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[inline_lower_instruction_def] >> qexists `fn` >> simp[]
QED

Theorem inline_rewrite_counter:
  !insts k. k <= LENGTH args ==>
    SND (rewrite_inline_insts args outs ret insts k) =
      MIN (LENGTH args)
        (k + LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts))
Proof
  Induct_on `insts`
  >- simp[rewrite_inline_insts_def, arithmeticTheory.MIN_EQ_LE] >>
  rpt strip_tac >>
  Cases_on `is_param_opcode h.inst_opcode` >>
  Cases_on `k < LENGTH args` >>
  Cases_on `h.inst_opcode = RET \/ h.inst_opcode = RETFMP` >>
  simp[rewrite_inline_inst_def, rewrite_inline_insts_def, pairTheory.UNCURRY] >>
  first_x_assum (qspec_then `if is_param_opcode h.inst_opcode /\ k < LENGTH args
    then k+1 else k` mp_tac) >> simp[] >>
  rpt strip_tac >>
  simp[pairTheory.UNCURRY, arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem inline_rewrite_prefix_counter:
  SND (rewrite_inline_insts args outs ret
    (MAP (clone_instruction p labs) (TAKE j insts)) 0) =
  MIN (LENGTH args)
    (LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) (TAKE j insts)))
Proof
  `!xs. LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode)
      (MAP (clone_instruction p labs) xs)) =
    LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) xs)` by
    (Induct >> simp[clone_instruction_def] >>
     Cases_on `is_param_opcode h.inst_opcode` >> simp[]) >>
  simp[inline_rewrite_counter]
QED

(* Exhausted argument lists retain physical parameters; placement is not
   preserved merely by the syntactic clone/rewrite operation. *)
Theorem inline_exhausted_parameter_survives:
  is_param_opcode inst.inst_opcode /\ LENGTH args <= k ==>
  rewrite_inline_inst args outs ret (clone_instruction p labs inst) k =
    ([clone_instruction p labs inst], k)
Proof
  simp[rewrite_inline_inst_def, clone_instruction_def]
QED

(* This boundary is about original canonical code, not cloned residual code. *)
Theorem inline_original_parameter_position:
  canonical_entry_params_from k insts /\ j < LENGTH insts /\
  is_param_opcode (EL j insts).inst_opcode ==>
  param_inst_at (k + j) (EL j insts)
Proof
  strip_tac >> drule canonical_entry_params_from_sound >> strip_tac >>
  rename1 `no_param_insts tail` >>
  qabbrev_tac `params = users ++ fmp ++ retpc` >>
  `insts = params ++ tail` by simp[Abbr `params`] >>
  `j < LENGTH params` by
    (spose_not_then assume_tac >>
     gvs[EL_APPEND_EQN, no_param_insts_def, EVERY_EL] >>
     first_x_assum (qspec_then `j - LENGTH params` mp_tac) >> simp[]) >>
  drule_all param_insts_from_el >> simp[EL_APPEND_EQN]
QED

(* PARAM and FMP_PARAM read the current activation's argument vector.
   RETPC_PARAM deliberately does not have this availability requirement. *)
Theorem inline_original_argument_step:
  MEM inst.inst_opcode [PARAM; FMP_PARAM] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] ==>
  (step_inst fuel ctx inst s = OK u <=>
   w2n idx < LENGTH s.vs_params /\
   u = update_var x (EL (w2n idx) s.vs_params) s)
Proof
  strip_tac >> gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `w2n idx < LENGTH s.vs_params` >> simp[] >> metis_tac[]
QED

Theorem inline_original_reached_argument:
  eval_operands ops caller = SOME vals /\
  setup_callee fn vals caller = SOME cs /\
  s.vs_params = cs.vs_params /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] /\
  step_inst fuel ctx inst s = r /\ (!e. r <> Error e) ==>
  w2n idx < LENGTH ops /\
  eval_operand (EL (w2n idx) ops) caller =
    SOME (EL (w2n idx) s.vs_params) /\
  r = OK (update_var x (EL (w2n idx) s.vs_params) s)
Proof
  strip_tac >>
  `is_param_opcode inst.inst_opcode` by gvs[is_param_opcode_def] >>
  drule step_inst_param_ok_or_error >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  strip_tac >> fs[] >>
  drule setup_callee_frame >> strip_tac >>
  `MEM inst.inst_opcode [PARAM; FMP_PARAM]` by simp[] >>
  drule_all inline_original_argument_step >> simp[] >> strip_tac >>
  drule eval_operands_length >> strip_tac >>
  drule eval_operands_index >>
  disch_then (qspec_then `w2n idx` mp_tac) >> gvs[]
QED

Theorem inline_original_reached_token:
  setup_callee fn vals caller = SOME cs /\
  s.vs_return_pc_token = cs.vs_return_pc_token /\
  inst.inst_opcode = RETPC_PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] ==>
  step_inst fuel ctx inst s =
    OK (update_var x (if NULL vals then 0w else LAST vals) s)
Proof
  strip_tac >> drule setup_callee_frame >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_def]
QED
