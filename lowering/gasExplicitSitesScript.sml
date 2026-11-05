(* Original/shadow raw-context comparison fixes the changed GAS sites.
   This static classification does not assert a selected source execution. *)
Theory gasExplicitSites
Ancestors
  gasShadowUnitObservations gasShadowUnit gasShadowState venomInst venomWf
  list pred_set

(* The set is determined by the original and shadow raw contexts. *)
Definition gas_explicit_sites_def:
  gas_explicit_sites c d =
    {site | ?f g i j.
      MEM f c.ctx_functions /\ MEM g d.ctx_functions /\
      MEM i (fn_insts f) /\ MEM j (fn_insts g) /\
      site = (f.fn_name, i.inst_id) /\
      f.fn_name = g.fn_name /\ i.inst_id = j.inst_id /\
      i.inst_opcode = GAS /\ j.inst_opcode = GASPRICE}
End

(* Global instruction IDs identify instructions even across functions. *)
Theorem ctx_inst_ids_distinct_inj:
  ctx_inst_ids_distinct ctx /\
  MEM f ctx.ctx_functions /\ MEM g ctx.ctx_functions /\
  MEM i (fn_insts f) /\ MEM j (fn_insts g) /\
  i.inst_id = j.inst_id ==> i = j
Proof
  rpt strip_tac >>
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
         FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
  qabbrev_tac `insts = FLAT (MAP fn_insts ctx.ctx_functions)` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) insts)` by
    gvs[Abbr `insts`, MAP_FLAT, MAP_COMPOSE, combinTheory.o_DEF,
        fn_insts_def, ctx_inst_ids_distinct_def] >>
  `MEM i insts /\ MEM j insts` by
    (simp[Abbr `insts`, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MEM f ctx.ctx_functions` kall_tac >>
  qpat_x_assum `MEM g ctx.ctx_functions` kall_tac >>
  qpat_x_assum `MEM i (fn_insts f)` kall_tac >>
  qpat_x_assum `MEM j (fn_insts g)` kall_tac >>
  fs[MEM_EL] >> rename1 `j = EL m _` >>
  `EL n (MAP (\i. i.inst_id) insts) =
   EL m (MAP (\i. i.inst_id) insts)` by gvs[EL_MAP] >>
  `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]
QED

Theorem gas_explicit_sites_classify:
  gas_shadow_context c d /\ ctx_inst_ids_distinct c /\
  MEM f c.ctx_functions /\ MEM g d.ctx_functions /\
  gas_shadow_function f g /\
  MEM i (fn_insts f) /\ MEM j (fn_insts g) /\
  gas_shadow_inst i j /\ i.inst_opcode = GAS ==>
  ((f.fn_name, i.inst_id) IN gas_explicit_sites c d <=>
   j.inst_opcode = GASPRICE)
Proof
  strip_tac >>
  `ctx_inst_ids_distinct d` by
    metis_tac[gas_shadow_ctx_inst_ids_distinct] >>
  drule gas_shadow_inst_fields >> strip_tac >>
  drule gas_shadow_function_fields >> strip_tac >>
  simp[gas_explicit_sites_def] >> eq_tac
  >- (strip_tac >>
      rename1 `MEM j' (fn_insts g')` >>
      `j' = j` by (irule ctx_inst_ids_distinct_inj >>
                   conj_tac >- simp[] >>
                   qexistsl [`d`, `g'`, `g`] >> simp[]) >>
      qpat_x_assum `j' = j` (SUBST_ALL_TAC) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl [`f`, `g`, `i`, `j`] >> simp[]
QED
