Theory lowerDloadPtrInvoke
Ancestors lowerDloadPtrJointEntry o1ContractLowerDload lowerDloadDefs
  lowerDloadPtrAggregate lowerDloadPtrAlloc lowerDloadPtrCall lowerDloadPtrRel ptrDiscipline
  venomWf
  venomExecSemantics venomState venomInst list rich_list pred_set

Theorem dload_param_values_cons:
  LENGTH PG = LENGTH xs /\ LENGTH PH = LENGTH ys /\
  dload_value_word fs {} p q x y /\ dload_param_values fs PG PH xs ys ==>
  dload_param_values fs (p::PG) (q::PH) (x::xs) (y::ys)
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN] >> strip_tac >>
  gen_tac >> Cases_on `n` >> simp[EL_GENLIST] >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[EL_GENLIST]
QED

Theorem dload_matched_operands_backwards:
  !ops ys.
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) ops ==> v IN V) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  eval_operands ops t = SOME ys ==>
  ?xs. eval_operands ops s = SOME xs /\
    LENGTH xs = LENGTH ops /\ LENGTH ys = LENGTH ops /\
    dload_param_values fs (MAP (op_prov G) ops) (MAP (op_prov H) ops) xs ys
Proof
  Induct_on `ops`
  >- simp[eval_operands_def, dload_param_values_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  rename1 `eval_operand h t = SOME y` >>
  `!v. h = Var v ==> v IN V` by metis_tac[] >>
  drule_all dload_matched_operand_defined >> strip_tac >>
  Cases_on `eval_operand h s` >- gvs[] >>
  rename1 `eval_operand h s = SOME x` >>
  `dload_value_word fs {} (op_prov G h) (op_prov H h) x y` by
    (drule_all dload_matched_operand >> simp[]) >>
  qexists_tac `x::xs` >>
  simp[eval_operands_def] >>
  irule dload_param_values_cons >> simp[]
QED

Theorem dload_invoke_setup_backwards:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  decode_invoke i = SOME (name,ops) /\ i.inst_opcode = INVOKE /\
  taint_ok caller tn i s /\ (!v. MEM (Var v) ops ==> v IN V) /\
  eval_operands ops t = SOME ys /\ ~NULL fn.fn_blocks /\
  setup_callee gn ys t = SOME ct ==>
  ?xs cs. eval_operands ops s = SOME xs /\
    setup_callee fn xs s = SOME cs /\
    dload_param_values fs (MAP (op_prov G) ops) (MAP (op_prov H) ops)
      cs.vs_params ct.vs_params
Proof
  rpt strip_tac >>
  `!op. MEM op ops ==> MEM op i.inst_operands` by
    (gvs[decode_invoke_def, AllCaseEqs()] >> simp[]) >>
  `!op. MEM op ops ==> op_taint tn op = {}` by
    metis_tac[dload_invoke_operand_untainted] >>
  drule_all dload_matched_operands_backwards >> strip_tac >>
  `?cs. setup_callee fn xs s = SOME cs` by simp[setup_callee_def] >>
  qexistsl_tac [`xs`, `cs`] >> simp[] >>
  drule_all dload_setup_parameters >> simp[]
QED

Theorem dload_live_site_empty_push:
  dload_live_site
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
    owner id b c n <=>
  ?k. owner = SUC k /\ dload_live_site fs k id b c n
Proof
  Cases_on `owner` >> simp[dload_live_site_def]
QED

Theorem dload_pointer_word_empty_push:
  dload_pointer_word
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
    a b x y <=> dload_pointer_word fs a b x y
Proof
  PairCases_on `a` >> PairCases_on `b` >>
  simp[dload_pointer_word_def, dload_live_site_empty_push] >> metis_tac[]
QED

Theorem dload_value_word_empty_push:
  dload_value_word
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
    mask p q x y <=> dload_value_word fs mask p q x y
Proof
  Cases_on `p` >> Cases_on `q` >>
  simp[dload_value_word_def, dload_pointer_word_empty_push]
QED

Theorem dload_param_values_empty_push:
  dload_param_values
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
    PG PH xs ys <=> dload_param_values fs PG PH xs ys
Proof
  simp[dload_param_values_def, dload_value_word_empty_push]
QED

Theorem dload_memory_match_setup_push:
  dload_memory_match lo fs tn un s t /\
  setup_callee fn xs s = SOME u /\ setup_callee gn ys t = SOME v ==>
  dload_memory_match lo
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
    (tn with t_var := FEMPTY) (un with t_var := FEMPTY) u v
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[] >>
  fs[dload_memory_match_def, dload_live_site_empty_push] >> metis_tac[]
QED

Theorem dload_vars_match_setup:
  setup_callee fn xs s = SOME u /\ setup_callee gn ys t = SOME v ==>
  dload_vars_match fs V FEMPTY FEMPTY
    (tn with t_var := FEMPTY) (un with t_var := FEMPTY) u v
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[] >>
  simp[dload_vars_match_def, lookup_var_def]
QED

Theorem dload_saved_metadata_push_head:
  dload_vars_match fs V G H tn un s t /\
  dload_param_values fs PG PH s.vs_params t.vs_params ==>
  dload_saved_metadata fs V
    <|cf_fn := caller; cf_inst := i; cf_state := s;
      cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>
    <|cf_fn := gcaller; cf_inst := i; cf_state := t;
      cf_params := PH; cf_prov := H; cf_tvar := un.t_var|>
Proof
  simp[dload_saved_metadata_def, dload_vars_match_def, op_taint_def] >>
  metis_tac[]
QED

Theorem dload_invoke_push_boundary:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  decode_invoke i = SOME (name,ops) /\ i.inst_opcode = INVOKE /\
  taint_ok caller tn i s /\ (!v. MEM (Var v) ops ==> v IN V) /\
  eval_operands ops t = SOME ys /\ ~NULL fn.fn_blocks /\
  setup_callee gn ys t = SOME v /\
  (HD fn.fn_blocks).bb_label = (HD gn.fn_blocks).bb_label ==>
  ?xs u. eval_operands ops s = SOME xs /\ setup_callee fn xs s = SOME u /\
    dload_boundary_core lo
      (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
      Vcallee (V::Ws) (MAP (op_prov G) ops) (MAP (op_prov H) ops)
      FEMPTY FEMPTY (tn with t_var := FEMPTY) (un with t_var := FEMPTY) u v
      (<|cf_fn := caller; cf_inst := i; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: cs)
      (<|cf_fn := gcaller; cf_inst := i; cf_state := t;
         cf_params := PH; cf_prov := H; cf_tvar := un.t_var|> :: ds)
Proof
  rpt strip_tac >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `dload_equal_environment s t` by metis_tac[dload_boundary_environment] >>
  `s.vs_labels = t.vs_labels` by metis_tac[dload_equal_environment_code] >>
  drule_all dload_invoke_setup_backwards >> strip_tac >>
  qexistsl_tac [`xs`, `cs'`] >> simp[] >>
  `dload_memory_match lo
     (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
     (tn with t_var := FEMPTY) (un with t_var := FEMPTY) cs' v` by
    metis_tac[dload_memory_match_setup_push, dload_boundary_memory] >>
  `dload_vars_match
     (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
     Vcallee FEMPTY FEMPTY (tn with t_var := FEMPTY) (un with t_var := FEMPTY) cs' v` by
    metis_tac[dload_vars_match_setup] >>
  `dload_equal_environment cs' v` by metis_tac[dload_equal_environment_setup] >>
  `dload_shared_store tn un cs' v` by
    metis_tac[dload_shared_store_setup, dload_boundary_shared_store] >>
  `dload_shared_store (tn with t_var := FEMPTY) (un with t_var := FEMPTY) cs' v` by
    (gvs[dload_shared_store_def] >> metis_tac[]) >>
  `cs'.vs_alloca_next = s.vs_alloca_next /\
   v.vs_alloca_next = t.vs_alloca_next` by
    metis_tac[dload_setup_local_frame] >>
  fs[dload_boundary_core_def] >>
  simp[dload_boundary_core_def, dload_param_values_empty_push] >>
  conj_tac >- metis_tac[dload_layout_call_push] >>
  conj_tac
  >- (Cases_on `fs` >- fs[dload_table_stack_def] >>
      irule dload_table_call_push >> metis_tac[]) >>
  gen_tac >> Cases_on `k` >> simp[]
  >- metis_tac[dload_saved_metadata_push_head] >>
  metis_tac[]
QED

Theorem dload_setup_no_phi_entry:
  setup_callee fn xs s = SOME u /\ first_block_no_phi fn ==>
  (enters_block fn u u' <=> u' = u)
Proof
  rpt strip_tac >>
  `fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label` by
    (gvs[setup_callee_def, fn_entry_label_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  drule_all dload_no_phi_entry >>
  disch_then (qspec_then `u` mp_tac) >>
  gvs[setup_callee_def]
QED

(* Local call-constructor closure, not a global simulation hypothesis.
   In the joint induction, core/reachability come from the boundary anchor;
   taint_ok from source reachable safety; decoded trackedness from retpc-use
   restrictions; callee lookup/supply from stage lookup; and entry shape and
   distinct labels from source/stage shape.  Empty PHI entry makes setup itself
   the entry state, so call-rule ghosts are exactly FEMPTY and cleared t_var.
   The target call uses the same unchanged INVOKE record callinst. *)
Theorem dload_actual_invoke_call:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  frame_reachable vs0 C cs PG G tn caller callinst s /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (name,ops) /\
  taint_ok caller tn callinst s /\ (!a. MEM (Var a) ops ==> a IN V) /\
  lookup_function name C.ctx_functions = SOME callee /\
  lower_dload_function_supply q callee = (gcallee,q') /\
  first_block_no_phi callee /\ ~NULL callee.fn_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gcallee.fn_blocks) /\
  eval_operands ops t = SOME ys /\ setup_callee gcallee ys t = SOME v /\
  enters_block gcallee v t1 /\ active_inst gcallee j t1 ==>
  ?xs u i emitted.
    eval_operands ops s = SOME xs /\ setup_callee callee xs s = SOME u /\
    enters_block callee u u /\
    frame_reachable vs0 C
      (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: cs)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee i u /\
    (!a. lookup_var a u = NONE <=> lookup_var a t1 = NONE) /\
    dload_boundary_core lo
      (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
      {a | ~retpc_var callee a} (V::Ws)
      (MAP (op_prov G) ops) (MAP (op_prov H) ops)
      FEMPTY FEMPTY (tn with t_var := FEMPTY) (un with t_var := FEMPTY) u t1
      (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: cs)
      (<|cf_fn := gcaller; cf_inst := callinst; cf_state := t;
         cf_params := PH; cf_prov := H; cf_tvar := un.t_var|> :: ds) /\
    dload_control_match q callee gcallee u t1 i emitted 0 /\ j = HD emitted
Proof
  rpt strip_tac >>
  `first_block_no_phi gcallee` by
    (irule lower_dload_function_supply_first_no_phi >> metis_tac[NULL_EQ]) >>
  `t1 = v` by metis_tac[dload_setup_no_phi_entry] >> gvs[] >>
  `(HD callee.fn_blocks).bb_label = (HD gcallee.fn_blocks).bb_label` by
    (drule lower_dload_function_supply_labels >>
     simp[fn_entry_label_def, entry_block_def] >>
     Cases_on `callee.fn_blocks` >> Cases_on `gcallee.fn_blocks` >> gvs[]) >>
  drule_all dload_invoke_push_boundary >>
  disch_then (qspecl_then [`gcaller`, `{a | ~retpc_var callee a}`] strip_assume_tac) >>
  `enters_block callee u u` by metis_tac[dload_setup_no_phi_entry] >>
  `u.vs_current_bb = t1.vs_current_bb /\ u.vs_prev_bb = t1.vs_prev_bb` by
    (gvs[setup_callee_def]) >>
  drule_all dload_enters_block_control_match >> strip_tac >>
  `active_inst callee i u` by metis_tac[dload_control_match_boundary] >>
  qexistsl_tac [`xs`, `u`, `i`, `emitted`] >> simp[] >>
  conj_tac >- (irule frame_reachable_call >> metis_tac[]) >>
  imp_res_tac dload_setup_local_frame >> simp[lookup_var_def]
QED
