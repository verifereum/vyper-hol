Theory lowerDloadPtrNormalPush
Ancestors lowerDloadPtrInvoke lowerDloadPtrAggregate lowerDloadPtrSupport pred_set
  o1ContractLowerDload venomExecSemantics list rich_list

(* Interface probe for the active set delivered by actual invoke. *)
Theorem dload_invoke_active_set_probe[local]:
  dload_boundary_core lo fs {a | ~retpc_var callee a} Ws
    PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs
    (set (fn_ir_vars callee) DIFF {a | retpc_var callee a}) Ws
    PG PH G H tn un s t cs ds
Proof
  strip_tac >> irule dload_boundary_vars_restrict >>
  goal_assum (drule_at Any) >> simp[SUBSET_DEF]
QED

Theorem dload_scratch_stack_push:
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                i.inst_id = id}) /\
  v.vs_allocas = FEMPTY /\ fr.dr_scratch = {} /\
  c.cf_fn = f /\ d.cf_state = t ==>
  LENGTH (fr::fs) = SUC (LENGTH (c::cs)) /\
  LENGTH (c::cs) = LENGTH (d::ds) /\
  (!k. k < LENGTH (fr::fs) ==>
    (EL k (fr::fs)).dr_scratch =
      FDOM (EL k (v::MAP (\d. d.cf_state) (d::ds))).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (callee::MAP (\c. c.cf_fn) (c::cs)))) /\
                i.inst_id = id})
Proof
  strip_tac >> simp[] >> Cases >> simp[]
QED

(* The saved suffix contains no observation of the active frame except the
   address parameter. Abstract the rest once for both push and head change. *)
Theorem dload_saved_suffix_push:
  (!k. k < LENGTH cs ==> R (DROP (SUC k) fs) (EL k cs) (EL k ds)) ==>
  !k. k < LENGTH cs ==>
    R (DROP (SUC (SUC k)) (fr::fs))
      (EL (SUC k) (c::cs)) (EL (SUC k) (d::ds))
Proof
  simp[]
QED

Theorem dload_saved_suffix_head_change:
  (!k. k < LENGTH cs ==> R addr (DROP (SUC k) (fr::fs)) (EL k cs) (EL k ds)) /\
  addr' = addr ==>
  !k. k < LENGTH cs ==>
    R addr' (DROP (SUC k) (fr'::fs)) (EL k cs) (EL k ds)
Proof
  simp[]
QED

Theorem dload_normal_invoke_call:
  dload_boundary_core lo fs
    (set (fn_ir_vars caller) DIFF {a | retpc_var caller a})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {a | retpc_var c.cf_fn a}) cs)
    PG PH G H tn un s t cs ds /\
  frame_reachable vs0 C cs PG G tn caller callinst s /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (name,ops) /\
  taint_ok caller tn callinst s /\
  (!a. MEM (Var a) ops ==>
    a IN (set (fn_ir_vars caller) DIFF {a | retpc_var caller a})) /\
  lookup_function name C.ctx_functions = SOME callee /\
  lower_dload_function_supply q callee = (gcallee,q') /\
  first_block_no_phi callee /\ ~NULL callee.fn_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gcallee.fn_blocks) /\
  eval_operands ops t = SOME ys /\ setup_callee gcallee ys t = SOME v /\
  enters_block gcallee v t1 /\ active_inst gcallee j t1 /\
  ir_supply_covers_fn q callee /\
  ir_supply_covers_fn qc caller /\
  lower_dload_function_supply qc caller = (gcaller,qc') /\
  dload_control_match qc caller gcaller s t callinst [callinst] 0 /\
  (!a. a IN set (fn_ir_vars caller) ==>
    (lookup_var a s = NONE <=> lookup_var a t = NONE)) /\
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (caller::MAP (\c. c.cf_fn) cs))) /\
                i.inst_id = id}) /\
  (!k. k < LENGTH cs ==>
    let c = EL k cs; d = EL k ds in
    dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
      (DROP (SUC k) fs) /\
    dload_equal_environment c.cf_state d.cf_state /\
    c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    c.cf_inst = d.cf_inst /\
    (!a. a IN set (fn_ir_vars c.cf_fn) ==>
      (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
    (?q. ir_supply_covers_fn q c.cf_fn /\
      (?q'. lower_dload_function_supply q c.cf_fn = (d.cf_fn,q')) /\
      dload_control_match q c.cf_fn d.cf_fn c.cf_state d.cf_state
        c.cf_inst [c.cf_inst] 0)) /\
  (!f. MEM f C.ctx_functions ==> fn_ptr_ok P f) ==>
  ?xs u i emitted.
    let c = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
              cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>;
        d = <|cf_fn := gcaller; cf_inst := callinst; cf_state := t;
              cf_params := PH; cf_prov := H; cf_tvar := un.t_var|>;
        fr = <|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>
    in
    eval_operands ops s = SOME xs /\ setup_callee callee xs s = SOME u /\
    enters_block callee u u /\
    frame_reachable vs0 C (c::cs) (MAP (op_prov G) ops) FEMPTY
      (tn with t_var := FEMPTY) callee i u /\
    (!a. a IN set (fn_ir_vars callee) ==>
      (lookup_var a u = NONE <=> lookup_var a t1 = NONE)) /\
    dload_boundary_core lo (fr::fs)
      (set (fn_ir_vars callee) DIFF {a | retpc_var callee a})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {a | retpc_var c.cf_fn a}) (c::cs))
      (MAP (op_prov G) ops) (MAP (op_prov H) ops) FEMPTY FEMPTY
      (tn with t_var := FEMPTY) (un with t_var := FEMPTY) u t1 (c::cs) (d::ds) /\
    dload_control_match q callee gcallee u t1 i emitted 0 /\ j = HD emitted /\
    ir_supply_covers_fn q callee /\
    lower_dload_function_supply q callee = (gcallee,q') /\
    LENGTH (fr::fs) = SUC (LENGTH (c::cs)) /\ LENGTH (c::cs) = LENGTH (d::ds) /\
    (!k. k < LENGTH (fr::fs) ==>
      (EL k (fr::fs)).dr_scratch =
        FDOM (EL k (t1::MAP (\d. d.cf_state) (d::ds))).vs_allocas DIFF
        {id | ?i. MEM i (fn_insts (EL k (callee::MAP (\c. c.cf_fn) (c::cs)))) /\
                  i.inst_id = id}) /\
    (!k. k < LENGTH (c::cs) ==>
      let c = EL k (c::cs); d = EL k (d::ds) in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) (fr::fs)) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = u.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?q. ir_supply_covers_fn q c.cf_fn /\
        (?q'. lower_dload_function_supply q c.cf_fn = (d.cf_fn,q')) /\
        dload_control_match q c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0)) /\
    FDOM (FEMPTY:string |-> num # num) SUBSET fn_pv P callee /\
    (!k b sz. k < LENGTH (MAP (op_prov G) ops) /\
      EL k (MAP (op_prov G) ops) = SOME (b,sz) ==> k IN P callee.fn_name) /\
    (!cc. MEM cc (c::cs) ==> FDOM cc.cf_prov SUBSET fn_pv P cc.cf_fn) /\
    (!cc k b sz. MEM cc (c::cs) /\ k < LENGTH cc.cf_params /\
      EL k cc.cf_params = SOME (b,sz) ==> k IN P cc.cf_fn.fn_name)
Proof
  rpt strip_tac >>
  drule_all dload_actual_invoke_call >>
  disch_then (qspec_then `gcaller` strip_assume_tac) >>
  drule_all dload_invoke_active_set_probe >> strip_tac >>
  `t1 = v` by
    (`first_block_no_phi gcallee` by
       (irule lower_dload_function_supply_first_no_phi >>
        qexistsl_tac [`callee`, `q`, `q'`] >> gvs[NULL_EQ]) >>
     qpat_assum `setup_callee gcallee ys t = SOME v`
       (mp_then Any mp_tac dload_setup_no_phi_entry) >> simp[] >>
     disch_then (qspec_then `t1` mp_tac) >> simp[]) >>
  `t1.vs_allocas = FEMPTY /\
   u.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    (gvs[setup_callee_def]) >>
  qexistsl_tac [`xs`, `u`, `i`, `emitted`] >> gvs[] >>
  conj_tac >- suspend "stack" >>
  conj_tac >- suspend "saved" >>
  suspend "support"
QED

Resume dload_normal_invoke_call[stack]:
  Cases >> simp[]
QED

Resume dload_normal_invoke_call[saved]:
  qpat_assum `dload_boundary_core lo fs _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any strip_assume_tac dload_boundary_layout) >>
  qpat_assum `dload_boundary_core lo fs _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any strip_assume_tac dload_boundary_environment) >>
  Cases >- (simp[] >> qexists_tac `qc` >> simp[]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!k. k < LENGTH ds ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume dload_normal_invoke_call[support]:
  qpat_assum `frame_reachable vs0 C (_::cs) _ _ _ callee i u`
    (mp_then Any mp_tac frame_reachable_prov_supported) >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >>
  strip_tac >> rpt conj_tac >> rpt strip_tac >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Finalise dload_normal_invoke_call
