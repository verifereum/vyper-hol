(* Candidate joint induction interface. Establishment and preservation are
   separate obligations; these definitions assert no execution theorem. *)
Theory o1LowerDloadJointRelation
Ancestors
  o1LowerDloadOccurrence o1LowerDloadEnvironment o1LowerDloadShared
  o1LowerDloadMapEvolution lowerDloadDefs irSupply
  ptrDiscipline venomExecSemantics finite_map words list pred_set

Definition ld_joint_erasure_def:
  ld_joint_erasure sites B <=>
    FDOM sites = FDOM B /\
    !id b c z. FLOOKUP sites id = SOME (b,c,z) ==>
      FLOOKUP B id = SOME (b,z)
End

Definition ld_joint_control_def:
  ld_joint_control u fn fn' s t <=>
    ir_supply_covers_fn u fn /\
    (?u'. lower_dload_function_supply u fn = (fn',u')) /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    ?k bb pre u1 bb' u2 expanded u3.
      k < LENGTH fn.fn_blocks /\ bb = EL k fn.fn_blocks /\
      bb.bb_label = s.vs_current_bb /\
      lower_dload_blocks_supply u (TAKE k fn.fn_blocks) = (pre,u1) /\
      lower_dload_block_supply u1 bb = (bb',u2) /\
      k < LENGTH fn'.fn_blocks /\ EL k fn'.fn_blocks = bb' /\
      s.vs_inst_idx < LENGTH bb.bb_instructions /\
      lower_dload_insts_supply u1 (TAKE s.vs_inst_idx bb.bb_instructions) =
        (expanded,u3) /\ t.vs_inst_idx = LENGTH expanded
End

(* A scratch key identifies an actual generated ALLOCA, not an arbitrary aid. *)
Definition ld_joint_scratch_def:
  ld_joint_scratch u fn did aid <=>
    ?k bb pre u1 j inst before u2 expansion u3.
      k < LENGTH fn.fn_blocks /\ bb = EL k fn.fn_blocks /\
      lower_dload_blocks_supply u (TAKE k fn.fn_blocks) = (pre,u1) /\
      j < LENGTH bb.bb_instructions /\ inst = EL j bb.bb_instructions /\
      inst.inst_id = did /\ inst.inst_opcode = DLOAD /\
      (?p out. inst.inst_operands = [p] /\ inst.inst_outputs = [out]) /\
      lower_dload_insts_supply u1 (TAKE j bb.bb_instructions) = (before,u2) /\
      lower_dload_inst_supply u2 inst = (expansion,u3) /\
      expansion <> [] /\ (HD expansion).inst_id = aid /\
      (HD expansion).inst_opcode = ALLOCA /\
      (HD expansion).inst_operands = [Lit 32w]
End

(* Exact owner-local partition of target allocations. *)
Definition ld_joint_allocas_def:
  ld_joint_allocas sites X owner fn t <=>
    (!aid c z. FLOOKUP t.vs_allocas aid = SOME (c,z) <=>
       (?b. FLOOKUP sites (owner,aid) = SOME (b,c,z)) \/
       (?did. FLOOKUP X (owner,did) = SOME (aid,c) /\ z = 32)) /\
    (!did aid c. FLOOKUP X (owner,did) = SOME (aid,c) ==>
       ~MEM aid (fn_ir_inst_ids fn)) /\
    (!d e aid c c'. FLOOKUP X (owner,d) = SOME (aid,c) /\
       FLOOKUP X (owner,e) = SOME (aid,c') ==> d = e) /\
    (!aid b c z. FLOOKUP sites (owner,aid) = SOME (b,c,z) ==>
       MEM aid (fn_ir_inst_ids fn))
End

Definition ld_joint_local_fields_def:
  ld_joint_local_fields s t <=>
    s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
    s.vs_block_ctx = t.vs_block_ctx /\
    s.vs_data_section = t.vs_data_section /\ s.vs_labels = t.vs_labels /\
    s.vs_code = t.vs_code /\ s.vs_fmp = t.vs_fmp /\
    s.vs_initial_fmp = t.vs_initial_fmp /\
    s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
    s.vs_prev_hashes = t.vs_prev_hashes /\ s.vs_halted = t.vs_halted
End

Definition ld_joint_frame_def:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv s t <=>
    ld_env_agree sites fn H (entry_taint with t_var := tv) s t /\
    ld_params_agree sites HP s t /\ ld_joint_local_fields s t /\
    ld_joint_control u fn fn' s t /\ ld_joint_allocas sites X owner fn t /\
    (!did aid c. FLOOKUP X (owner,did) = SOME (aid,c) ==>
       ld_joint_scratch u fn did aid) /\
    (!aid b c z. FLOOKUP sites (owner,aid) = SOME (b,c,z) ==>
       b+z <= s.vs_alloca_next /\ c+z <= t.vs_alloca_next) /\
    (!did aid c. FLOOKUP X (owner,did) = SOME (aid,c) ==>
       c+32 <= t.vs_alloca_next) /\
    lo <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
    t.vs_alloca_next < dimword (:256) /\
    t.vs_alloca_next = s.vs_alloca_next +
      32 * CARD {id | id IN FDOM X /\ MEM (FST id) (owner::older)}
End

Definition ld_joint_saved_def:
  (ld_joint_saved C' sites X lo [] stk ts <=> stk = [] /\ ts = []) /\
  (ld_joint_saved C' sites X lo (ofr::os) stk ts <=>
    ?f fs t rest u fn'. stk = f::fs /\ ts = t::rest /\
      lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fn' /\
      ld_joint_frame sites X lo ofr.of_owner (MAP (\x. x.of_owner) os)
        u f.cf_fn fn' ofr.of_prov ofr.of_params f.cf_tvar f.cf_state t /\
      ld_joint_saved C' sites X lo os fs rest)
End

Definition ld_joint_geometry_def:
  ld_joint_geometry sites X lo owners <=>
    (!id. id IN FDOM sites \/ id IN FDOM X ==> MEM (FST id) owners) /\
    (!id b c z. FLOOKUP sites id = SOME (b,c,z) ==>
       lo <= b /\ lo <= c /\ b+z < dimword (:256) /\ c+z < dimword (:256)) /\
    (!id aid c. FLOOKUP X id = SOME (aid,c) ==>
       lo <= c /\ c+32 < dimword (:256)) /\
    (!id jd b c z d e w.
       FLOOKUP sites id = SOME (b,c,z) /\ FLOOKUP sites jd = SOME (d,e,w) /\
       id <> jd /\ 0 < z /\ 0 < w ==>
       (b+z <= d \/ d+w <= b) /\ (c+z <= e \/ e+w <= c)) /\
    (!id jd b c z aid e.
       FLOOKUP sites id = SOME (b,c,z) /\ FLOOKUP X jd = SOME (aid,e) /\
       0 < z ==> c+z <= e \/ e+32 <= c) /\
    (!id jd aid c bid d.
       FLOOKUP X id = SOME (aid,c) /\ FLOOKUP X jd = SOME (bid,d) /\
       id <> jd ==> c+32 <= d \/ d+32 <= c)
End

Definition ld_joint_boundary_def:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
      n a U B HP H sites X ts <=>
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
    occurrence_annotation_ok n a U B HP H stk PG G s /\
    ld_joint_erasure sites B /\
    ld_joint_geometry sites X lo (a::MAP (\x. x.of_owner) U) /\
    (?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       ld_joint_frame sites X lo a (MAP (\x. x.of_owner) U)
         u fn fn' H HP tn.t_var s t) /\
    ld_joint_saved C' sites X lo U stk ts /\
    ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
    s.vs_returndata = t.vs_returndata
End

Theorem ld_joint_source:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H
Proof
  simp[ld_joint_boundary_def]
QED

Theorem ld_joint_erasure_lookup:
  ld_joint_erasure sites B ==>
  (FLOOKUP B id = SOME (b,z) <=> ?c. FLOOKUP sites id = SOME (b,c,z))
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      `id IN FDOM sites` by gvs[ld_joint_erasure_def, FLOOKUP_DEF] >>
      Cases_on `FLOOKUP sites id` >- gvs[FLOOKUP_DEF] >>
      rename1 `FLOOKUP sites id = SOME triple` >> PairCases_on `triple` >>
      gvs[ld_joint_erasure_def] >> first_x_assum drule >> simp[]) >>
  gvs[ld_joint_erasure_def] >> metis_tac[]
QED

(* Generic owner-local consequence, reused by active and suspended frames. *)
Theorem ld_joint_frame_site:
  ld_joint_erasure sites B /\ occurrence_allocas_ok B owner s /\
  ld_joint_allocas sites X owner fn t /\
  FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  ?c. FLOOKUP sites (owner,aid) = SOME (b,c,z) /\
      FLOOKUP t.vs_allocas aid = SOME (c,z)
Proof
  strip_tac >>
  `FLOOKUP B (owner,aid) = SOME (b,z)` by
    gvs[occurrence_allocas_ok_def] >>
  drule ld_joint_erasure_lookup >>
  disch_then (qspecl_then [`z`, `(owner,aid)`, `b`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `c` >>
  gvs[ld_joint_allocas_def] >> metis_tac[]
QED

Theorem ld_joint_frame_lookup:
  ld_joint_erasure sites B /\ occurrence_allocas_ok B owner s /\
  ld_joint_allocas sites X owner fn t /\ MEM aid (fn_ir_inst_ids fn) ==>
  (FLOOKUP s.vs_allocas aid = NONE <=> FLOOKUP t.vs_allocas aid = NONE)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> Cases_on `FLOOKUP t.vs_allocas aid` >> simp[] >>
      rename1 `FLOOKUP t.vs_allocas aid = SOME pair` >> PairCases_on `pair` >>
      `?b. FLOOKUP sites (owner,aid) = SOME (b,pair0,pair1)` by
        (fs[ld_joint_allocas_def] >> metis_tac[]) >>
      fs[ld_joint_erasure_def] >>
      qpat_x_assum `!id b c z. _` drule >>
      gvs[occurrence_allocas_ok_def]) >>
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >> simp[] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME pair` >> PairCases_on `pair` >>
  drule_all ld_joint_frame_site >> simp[]
QED

Theorem ld_joint_original_site:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ FLOOKUP s.vs_allocas aid = SOME (b,z) ==>
  ?c. FLOOKUP sites (a,aid) = SOME (b,c,z) /\
      FLOOKUP t.vs_allocas aid = SOME (c,z)
Proof
  simp[ld_joint_boundary_def, occurrence_annotation_ok_def, ld_joint_frame_def] >>
  rpt strip_tac >> drule_all ld_joint_frame_site >> simp[]
QED

Theorem ld_joint_original_lookup:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ MEM aid (fn_ir_inst_ids fn) ==>
  (FLOOKUP s.vs_allocas aid = NONE <=> FLOOKUP t.vs_allocas aid = NONE)
Proof
  simp[ld_joint_boundary_def, occurrence_annotation_ok_def, ld_joint_frame_def] >>
  rpt strip_tac >> drule_all ld_joint_frame_lookup >> simp[]
QED

Theorem ld_joint_environment:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==> ld_env_agree sites fn H tn s t
Proof
  simp[ld_joint_boundary_def, ld_joint_frame_def] >>
  rpt strip_tac >> gvs[ld_env_agree_def, op_taint_def]
QED

Theorem ld_joint_labels:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==> s.vs_labels = t.vs_labels
Proof
  simp[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  rpt strip_tac >> simp[]
QED

Theorem ld_joint_operand_defined:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) ==>
  (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))
Proof
  strip_tac >> irule ld_env_operand_defined >>
  metis_tac[ld_joint_environment, ld_joint_labels]
QED

Theorem ld_joint_operand_value:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
  (!v. op = Var v ==> ~retpc_var fn v) /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      ld_value_agree sites (op_prov H op) (op_taint tn op) x y
Proof
  strip_tac >> irule ld_env_operand_value >>
  metis_tac[ld_joint_environment, ld_joint_labels]
QED

(* The same projection applies successively to every saved caller. Mutable
   shared observations and memory deliberately do not occur here. *)
Theorem ld_joint_saved_head:
  ld_joint_saved C' sites X lo (ofr::U) (f::stk) (t::ts) /\
  occurrence_saved_ok B (ofr::U) (f::stk) /\ ld_joint_erasure sites B ==>
  ld_env_agree sites f.cf_fn ofr.of_prov
    (entry_taint with t_var := f.cf_tvar) f.cf_state t /\
  ld_params_agree sites ofr.of_params f.cf_state t /\
  (!aid. MEM aid (fn_ir_inst_ids f.cf_fn) ==>
    (FLOOKUP f.cf_state.vs_allocas aid = NONE <=>
     FLOOKUP t.vs_allocas aid = NONE)) /\
  (!aid b z. FLOOKUP f.cf_state.vs_allocas aid = SOME (b,z) ==>
    ?c. FLOOKUP sites (ofr.of_owner,aid) = SOME (b,c,z) /\
        FLOOKUP t.vs_allocas aid = SOME (c,z)) /\
  ld_joint_saved C' sites X lo U stk ts /\ occurrence_saved_ok B U stk
Proof
  simp[ld_joint_saved_def, occurrence_saved_ok_def, ld_joint_frame_def] >>
  rpt strip_tac >>
  metis_tac[ld_joint_frame_lookup, ld_joint_frame_site]
QED

Theorem ld_joint_saved_projection:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  ld_joint_saved C' sites X lo U stk ts /\
  occurrence_saved_ok B U stk /\ ld_joint_erasure sites B
Proof
  simp[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  rpt strip_tac >> simp[]
QED

Theorem ld_joint_operand_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  op_prov H op = NONE /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> irule ld_env_operand_clean >>
  metis_tac[ld_joint_environment, ld_joint_labels]
QED
