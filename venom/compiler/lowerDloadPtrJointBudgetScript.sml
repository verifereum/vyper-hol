Theory lowerDloadPtrJointBudget
Ancestors
  lowerDloadPtrRuntimeSupport lowerDloadPtrLiveFrames lowerDloadPtrBudget
  lowerDloadPtrAlloc lowerDloadDefs ptrDiscipline o1PassContract
  venomState finite_map list pred_set

Theorem dload_joint_anchored_runtime_scratch_budget:
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g j t /\
  FDOM t0.vs_allocas SUBSET FDOM t.vs_allocas /\
  vs.vs_allocas = FEMPTY /\ callee_first names C.ctx_functions /\
  LENGTH fs = LENGTH (f::MAP (\c. c.cf_fn) cs) /\
  LENGTH (f::MAP (\c. c.cf_fn) cs) = LENGTH (g::MAP (\d. d.cf_fn) ds) /\
  (!k. k < LENGTH (f::MAP (\c. c.cf_fn) cs) ==>
    ?q q'. lower_dload_function_supply q (EL k (f::MAP (\c. c.cf_fn) cs)) =
      (EL k (g::MAP (\d. d.cf_fn) ds),q')) /\
  (!k. k < LENGTH fs ==> (EL k fs).dr_scratch =
    FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {ci.inst_id | MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs)))}) ==>
  SUM (MAP (\r. CARD r.dr_scratch) fs) <= ctx_dload_count C
Proof
  strip_tac >>
  `FDOM t.vs_allocas SUBSET set (MAP (\i. i.inst_id)
     (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts g))) /\
   EVERY (\c. FDOM c.cf_state.vs_allocas SUBSET set (MAP (\i. i.inst_id)
     (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts c.cf_fn)))) ds` by
    (qpat_assum `frame_reachable vs C' _ _ _ _ _ _ _`
       (mp_then Any mp_tac dload_frame_alloca_support) >> simp[]) >>
  `!k. k < LENGTH fs ==> FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas
    SUBSET set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA)
      (fn_insts (EL k (g::MAP (\d. d.cf_fn) ds)))))` by
    (gen_tac >> strip_tac >> Cases_on `k` >> gvs[EVERY_EL, EL_MAP] >>
     metis_tac[SUBSET_TRANS]) >>
  `!k. k < LENGTH fs ==> CARD (EL k fs).dr_scratch <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
      (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))))` by
    (gen_tac >> strip_tac >>
     `?q q'. lower_dload_function_supply q (EL k (f::MAP (\c. c.cf_fn) cs)) =
       (EL k (g::MAP (\d. d.cf_fn) ds),q')` by metis_tac[] >>
     `FINITE (EL k fs).dr_scratch /\ CARD (EL k fs).dr_scratch <=
       LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
         (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))))` by
       (irule dload_function_scratch_budget >>
        qexistsl [`{ci.inst_id | MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs)))}`,
          `EL k (g::MAP (\d. d.cf_fn) ds)`,`q`,`q'`] >>
        simp[] >> conj_tac >- metis_tac[] >>
        `FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas SUBSET
          set (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA)
            (fn_insts (EL k (g::MAP (\d. d.cf_fn) ds)))))` by metis_tac[] >>
        gvs[SUBSET_DEF, MEM_MAP, MEM_FILTER] >> metis_tac[]) >> simp[]) >>
  drule_all dload_frame_live_indices >> strip_tac >>
  irule dload_live_scratch_count_bound >> qexists_tac `ks` >> simp[] >>
  gen_tac >> strip_tac >>
  `k < LENGTH ks /\ k < LENGTH fs` by gvs[] >>
  `EL (EL k ks) C.ctx_functions = EL k (f::MAP (\c. c.cf_fn) cs)` by
    (qpat_x_assum `MAP _ ks = _` (mp_tac o Q.AP_TERM `EL k`) >> simp[EL_MAP]) >>
  gvs[EVERY_EL]
QED

(* Budget premise origins:
   Source reachability and callee_first produce distinct live context indices.
   Target reachability with an empty initial allocation table produces current
   AND saved-frame table support; no active instruction at a saved state is
   assumed.  Paired supply correspondence bounds each supported outside-original
   domain using dload_function_scratch_budget.  Exact scratch-domain identity
   and live-stack length alignment remain relational premises.  No target
   callee_first, per-frame numerical bound or aggregate budget is assumed. *)

Theorem dload_joint_runtime_scratch_budget:
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g j t /\
  vs.vs_allocas = FEMPTY /\ callee_first names C.ctx_functions /\
  LENGTH fs = LENGTH (f::MAP (\c. c.cf_fn) cs) /\
  LENGTH (f::MAP (\c. c.cf_fn) cs) = LENGTH (g::MAP (\d. d.cf_fn) ds) /\
  (!k. k < LENGTH (f::MAP (\c. c.cf_fn) cs) ==>
    ?q q'. lower_dload_function_supply q (EL k (f::MAP (\c. c.cf_fn) cs)) =
      (EL k (g::MAP (\d. d.cf_fn) ds),q')) /\
  (!k. k < LENGTH fs ==> (EL k fs).dr_scratch =
    FDOM (EL k (t::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {ci.inst_id | MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs)))}) ==>
  SUM (MAP (\r. CARD r.dr_scratch) fs) <= ctx_dload_count C
Proof
  strip_tac >> irule dload_joint_anchored_runtime_scratch_budget >>
  conj_tac >- metis_tac[] >>
  qpat_assum `frame_reachable vs C _ _ _ _ _ _ _`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' _ _ _ _ _ _ _`
    (irule_at (Pat `frame_reachable`)) >>
  qexists_tac `t` >> simp[]
QED
