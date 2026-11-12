(*
 * O1 source safety up to a gas cut.
 *
 * o1_src_inv asks every reachable state of a run to be safe.  A run that is
 * only known to be safe until the n-th GAS read (a prefix of a semantic gas
 * mask) has the same facts for the states before that read: gas_cut n vs s
 * says s has popped fewer than n of vs's gas readings.  o1_ptr_safe_upto
 * keeps o1_src_inv's context-only facts and guards its pointer discipline
 * and taint bound by the cut; o1_safe_upto adds the whole-run DLOAD
 * headroom and the guarded raw memory and DLOAD offset facts.  Every n
 * holds when o1_src_inv does (o1_src_inv_safe_upto).
 *)
Theory o1SafeUpto
Ancestors
  o1PassContract memSafeRun contextRawReachable contextCodegenRel unitMemInv
  ptrDiscipline lowerDloadDefs staticLayoutDefs venomExecSemantics
  venomExecProofs venomState stateFrame list

Definition gas_cut_def:
  gas_cut n (vs:venom_state) (s:venom_state) <=>
    LENGTH vs.vs_gas_readings < n + LENGTH s.vs_gas_readings
End

(* ptr_discipline's clauses, each per-state one guarded by the cut. *)
Definition ptr_discipline_upto_def:
  ptr_discipline_upto (lo:num) n ctx vs <=>
    lo <= vs.vs_alloca_next /\
    (?P. EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           ctx.ctx_functions) /\
    !stk PG G tn fn inst s.
      frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s ==>
      access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
      allocas_from lo s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s)
End

(* taint_within's request clause and its halt clause (final_taint
   inlined), guarded by the cut at the pre-step state. *)
Definition taint_within_upto_def:
  taint_within_upto D n ctx vs <=>
    (!stk PG G tn fn inst s fuel s'.
       frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s /\
       active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel ctx inst s = OK s' /\
       LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
       tn.t_stor SUBSET
         D.d_stor s.vs_call_ctx.cc_address
           (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
       tn.t_trans SUBSET
         D.d_trans s.vs_call_ctx.cc_address
           (s.vs_transient s.vs_call_ctx.cc_address)) /\
    (!stk PG G tn fn inst s fuel s_h.
       frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s /\
       active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel ctx inst s = Halt s_h ==>
       (step_taint inst s s_h tn).t_stor SUBSET
         D.d_stor s_h.vs_call_ctx.cc_address
           (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
       (step_taint inst s s_h tn).t_trans SUBSET
         D.d_trans s_h.vs_call_ctx.cc_address
           (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
       (step_taint inst s s_h tn).t_imm SUBSET D.d_imm s_h.vs_immutables /\
       ret_taint tn inst s SUBSET D.d_ret s_h.vs_returndata)
End

(* The context facts and the guarded pointer and taint halves. *)
Definition o1_ptr_safe_upto_def:
  o1_ptr_safe_upto D lo n C vs <=>
    reserved_intervals_wf C.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ ~ctx_has_dalloca C /\
    fmp_free_ctx C /\ fixed_region_reserved lo C /\
    ptr_discipline_upto lo n C vs /\ taint_within_upto D n C vs
End

Definition o1_safe_upto_def:
  o1_safe_upto D lo n C vs <=>
    o1_ptr_safe_upto D lo n C vs /\ mem_inv dload_headroom_ok C vs /\
    (!fn inst s.
       raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
       raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s)
End

Theorem gas_cut_mono:
  m <= n /\ gas_cut m vs s ==> gas_cut n vs s
Proof
  rw[gas_cut_def]
QED

Theorem ptr_discipline_upto_mono:
  m <= n /\ ptr_discipline_upto lo n ctx vs ==> ptr_discipline_upto lo m ctx vs
Proof
  rw[ptr_discipline_upto_def] >> metis_tac[gas_cut_mono]
QED

Theorem taint_within_upto_mono:
  m <= n /\ taint_within_upto D n ctx vs ==> taint_within_upto D m ctx vs
Proof
  rw[taint_within_upto_def] >> metis_tac[gas_cut_mono]
QED

Theorem o1_ptr_safe_upto_mono:
  m <= n /\ o1_ptr_safe_upto D lo n C vs ==> o1_ptr_safe_upto D lo m C vs
Proof
  rw[o1_ptr_safe_upto_def] >>
  metis_tac[ptr_discipline_upto_mono, taint_within_upto_mono]
QED

Theorem o1_safe_upto_mono:
  m <= n /\ o1_safe_upto D lo n C vs ==> o1_safe_upto D lo m C vs
Proof
  rw[o1_safe_upto_def] >>
  metis_tac[gas_cut_mono, o1_ptr_safe_upto_mono]
QED

Theorem ptr_discipline_upto_whole:
  ptr_discipline lo ctx vs ==> !n. ptr_discipline_upto lo n ctx vs
Proof
  rw[ptr_discipline_def, ptr_discipline_upto_def] >> metis_tac[]
QED

Theorem taint_within_upto_whole:
  taint_within D ctx vs ==> !n. taint_within_upto D n ctx vs
Proof
  rw[taint_within_def, taint_within_upto_def] >>
  fs[final_taint_def] >> metis_tac[]
QED

Theorem o1_src_inv_ptr_safe_upto:
  o1_src_inv D C vs /\ fixed_region_reserved lo C /\
  ptr_discipline lo C vs ==>
  !n. o1_safe_upto D lo n C vs
Proof
  rw[o1_src_inv_def, o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  fs[mem_inv_raw_reachable] >>
  metis_tac[ptr_discipline_upto_whole, taint_within_upto_whole]
QED

Theorem o1_src_inv_safe_upto:
  o1_src_inv D C vs ==> ?lo. !n. o1_safe_upto D lo n C vs
Proof
  strip_tac >> drule o1_src_inv_ptr_safe_upto >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

(* Code and data section never change along a raw run. *)
Theorem raw_reachable_code_data:
  !vs C fn inst s. raw_reachable vs C fn inst s ==>
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rw[enters_block_def, setup_callee_def] >>
  imp_res_tac venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  imp_res_tac step_inst_ok_code_data >>
  gvs[setup_callee_def, AllCaseEqs()] >>
  qpat_x_assum `s_phi = _` (fn th => once_rewrite_tac [th]) >> simp[]
QED

(* A producer that checks DLOAD offsets against the data section (the
   mem_safe checker) gets o1_safe_upto's offset bound. *)
Theorem dload_offset_ok_upto_intro:
  code_layout_valid vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
     inst_dload_in_section inst s) ==>
  !fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    dload_offset_ok C fn inst s
Proof
  rw[dload_offset_ok_def] >>
  first_x_assum drule_all >> rw[inst_dload_in_section_def] >>
  drule raw_reachable_code_data >> strip_tac >>
  gvs[code_layout_valid_def] >>
  `dimword (:256) DIV 2 < dimword (:256)` by
    (irule arithmeticTheory.DIV_LESS >> simp[wordsTheory.ZERO_LT_dimword]) >>
  decide_tac
QED

(* At n past every reading the cut holds of every state. *)
Theorem gas_cut_whole[simp]:
  gas_cut (SUC (LENGTH vs.vs_gas_readings)) vs s
Proof
  simp[gas_cut_def]
QED

(* States with the same execution frame have popped the same readings. *)
Theorem gas_cut_execution_frame:
  gas_cut n vs s' /\ execution_frame s' = execution_frame s ==>
  gas_cut n vs s
Proof
  strip_tac >>
  `s'.vs_gas_readings = s.vs_gas_readings` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  fs[gas_cut_def]
QED

(* The whole-run facts are the guarded ones at that n. *)
Theorem ptr_discipline_upto_all:
  ptr_discipline_upto lo (SUC (LENGTH vs.vs_gas_readings)) ctx vs ==>
  ptr_discipline lo ctx vs
Proof
  rw[ptr_discipline_def, ptr_discipline_upto_def] >> metis_tac[]
QED

Theorem taint_within_upto_all:
  taint_within_upto D (SUC (LENGTH vs.vs_gas_readings)) ctx vs ==>
  taint_within D ctx vs
Proof
  rw[taint_within_def, taint_within_upto_def, final_taint_def] >>
  metis_tac[]
QED
