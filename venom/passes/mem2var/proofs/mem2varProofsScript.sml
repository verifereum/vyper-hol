Theory mem2varProofs
Ancestors
  venomFnInstsProofs mem2varDefs mem2varFrame mem2varInvariant basePtrProps pointerConfinedDefs passSimulationProps
  memLocDefs venomExecProofs venomInstProofs venomMemDefs venomMemProps
  basePtrDefs
  passSimulationDefs
  stateEquiv
  venomExecSemantics venomState venomWf
  venomInst venomInstProps
  dfgDefs
  finite_map list pred_set pair
  string ASCIInumbers
  passTransform
Libs
  HolKernel boolLib bossLib BasicProvers markerLib mem2varFrameLib

val _ = augment_srw_ss [mem2varFrameLib.frame_ss];


(* Helper: m2v_scan_step preserves the invariant in one step *)
Theorem m2v_scan_step_preserves:
  !dfg ctr promos fresh i c' p' f'.
    (!ao pvar sz. MEM (ao, pvar, sz) promos ==> pvar IN fresh) /\
    m2v_scan_step dfg (ctr, promos, fresh) i = (c', p', f') ==>
    (!ao pvar sz. MEM (ao, pvar, sz) p' ==> pvar IN f')
Proof
  rw[m2v_scan_step_def] >>
  gvs[AllCaseEqs()] >> metis_tac[IN_INSERT]
QED

(* Key invariant of the combined scan *)
Theorem m2v_scan_invariant:
  !xs dfg ctr0 promos0 fresh0.
    (!ao pvar sz. MEM (ao, pvar, sz) promos0 ==> pvar IN fresh0) ==>
    let res = FOLDL (m2v_scan_step dfg) (ctr0, promos0, fresh0) xs in
    (!ao pvar sz. MEM (ao, pvar, sz) (FST (SND res)) ==>
                  pvar IN (SND (SND res)))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  Cases_on `m2v_scan_step dfg (ctr0,promos0,fresh0) h` >>
  Cases_on `r` >> simp[] >>
  first_x_assum (qspecl_then [`dfg`,`q`,`q'`,`r''`] mp_tac) >>
  simp[LET_THM] >>
  (impl_tac >- metis_tac[m2v_scan_step_preserves]) >>
  simp[]
QED

Theorem m2v_promo_list_in_fresh_vars:
  !fn ao pvar sz. MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
    pvar IN m2v_fresh_vars fn
Proof
  rw[m2v_promo_list_def, m2v_fresh_vars_def, m2v_scan_def] >>
  mp_tac (Q.SPECL [`FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn)`,
    `dfg_build_function fn`, `0`, `[]`, `{}`] m2v_scan_invariant) >>
  simp[] >> metis_tac[]
QED

(* The sole scan preserves promotability of accumulated candidates. *)
Theorem m2v_promo_foldl_can_promote[local]:
  !xs dfg ctr0 promos0 fresh0.
    EVERY (\(ao,pvar,sz). m2v_can_promote_alloca ao (dfg_get_uses dfg ao))
          promos0 ==>
    EVERY (\(ao,pvar,sz). m2v_can_promote_alloca ao (dfg_get_uses dfg ao))
      (FST (SND (FOLDL (m2v_scan_step dfg) (ctr0,promos0,fresh0) xs)))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `m2v_scan_step dfg (ctr0,promos0,fresh0) h` >>
  Cases_on `r` >> simp[] >>
  first_x_assum irule >>
  gvs[m2v_scan_step_def, AllCaseEqs(), m2v_can_promote_alloca_def]
QED

Theorem m2v_promo_list_can_promote:
  !fn ao pvar sz.
    MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
    m2v_can_promote_alloca ao (dfg_get_uses (dfg_build_function fn) ao)
Proof
  rw[m2v_promo_list_def, m2v_scan_def] >>
  mp_tac (Q.SPECL [`FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn)`,
    `dfg_build_function fn`, `0`, `[]`, `{}`]
    m2v_promo_foldl_can_promote) >>
  simp[EVERY_MEM] >> disch_then drule >> simp[]
QED

(* ================================================================
   STRUCTURAL LEMMAS
   ================================================================ *)

Theorem m2v_transform_eq_fmt:
  !fn. m2v_transform_function_raw fn = function_map_transform (m2v_bt fn) fn
Proof
  simp[m2v_transform_function_raw_def, function_map_transform_def,
       m2v_bt_def, m2v_promo_list_def, LET_THM,
       ir_function_component_equality, MAP_EQ_f,
       basic_block_component_equality]
QED

Theorem m2v_bt_preserves_label:
  !fn bb. (m2v_bt fn bb).bb_label = bb.bb_label
Proof
  rw[m2v_bt_def, LET_THM]
QED

(* ================================================================
   EQUIVALENCE RELATION PROPERTIES
   ================================================================ *)

Theorem m2v_equiv_refl:
  !vars s. m2v_equiv vars s s
Proof
  rw[m2v_equiv_def]
QED

Theorem m2v_equiv_control_flow:
  !vars s1 s2. m2v_equiv vars s1 s2 ==>
    s1.vs_current_bb = s2.vs_current_bb /\
    (s1.vs_halted <=> s2.vs_halted)
Proof
  rw[m2v_equiv_def]
QED

(* m2v_inv reflexivity under fresh-undef: sync is vacuously true
   because IS_SOME (lookup_var pvar s) = F when pvar is fresh and undef *)
Theorem m2v_inv_refl:
  !fn s. m2v_fresh_undef fn s ==> m2v_inv fn s s
Proof
  rw[m2v_inv_def, m2v_equiv_refl, m2v_fresh_undef_def] >>
  drule m2v_promo_list_in_fresh_vars >> strip_tac >>
  res_tac >> fs[]
QED

Theorem m2v_inv_implies_equiv:
  !fn s1 s2. m2v_inv fn s1 s2 ==>
    m2v_equiv (m2v_fresh_vars fn) s1 s2
Proof
  rw[m2v_inv_def]
QED

Theorem m2v_inv_control_flow:
  !fn s1 s2. m2v_inv fn s1 s2 ==>
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_halted <=> s2.vs_halted)
Proof
  rw[m2v_inv_def, m2v_equiv_def]
QED

(* ================================================================
   P-PRESERVATION: original execution preserves m2v_fresh_undef
   ================================================================ *)

(* General list lemma: ALL_DISTINCT (MAP f l) implies f is injective on l *)
Theorem ALL_DISTINCT_MAP_IMP:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ (f x = f y) ==>
    x = y
Proof
  Induct_on `l` >> rw[] >> fs[MEM_MAP] >> metis_tac[]
QED

(* fn_inst_ids_distinct gives ALL_DISTINCT of MAP inst_id over fn_insts *)
Theorem fn_inst_ids_distinct_MAP[local]:
  !fn. fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  rw[fn_inst_ids_distinct_def, fn_insts_def] >>
  `!bbs. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs) =
     MAP (\i. i.inst_id) (fn_insts_blocks bbs)` suffices_by metis_tac[] >>
  Induct >> rw[fn_insts_blocks_def, MAP_FLAT, MAP_MAP_o]
QED

(* wf_function: same inst_id implies same instruction *)
Theorem wf_fn_inst_id_inj:
  !fn i1 i2. wf_function fn /\
    MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    (i1.inst_id = i2.inst_id) ==> i1 = i2
Proof
  rpt strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  drule fn_inst_ids_distinct_MAP >>
  metis_tac[ALL_DISTINCT_MAP_IMP]
QED

(* Key lemma: fresh var names are not in any block's instruction outputs *)
Theorem m2v_fresh_not_in_block_outputs:
  !fn bb v.
    m2v_fresh_names_disjoint fn /\ MEM bb fn.fn_blocks /\
    v IN m2v_fresh_vars fn ==>
    ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rw[m2v_fresh_names_disjoint_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_fn_insts]
QED

(* FOLDL invariant: promo entries come from ALLOCA instructions in xs *)
Theorem m2v_promo_foldl_is_alloca[local]:
  !xs dfg ctr0 promos0 fresh0.
    !ao pvar sz.
      MEM (ao,pvar,sz)
        (FST (SND (FOLDL (m2v_scan_step dfg) (ctr0,promos0,fresh0) xs))) ==>
      MEM (ao,pvar,sz) promos0 \/
      ?i. MEM i xs /\ i.inst_outputs = [ao] /\
          (case i.inst_operands of Lit w :: _ => w2n w | _ => 0) = sz /\
          (?w. i.inst_operands = [Lit w] /\ w2n w = sz)
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  Cases_on `m2v_scan_step dfg (ctr0,promos0,fresh0) h` >>
  Cases_on `r` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (gvs[m2v_scan_step_def, AllCaseEqs()] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem m2v_promo_list_is_alloca:
  !fn ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
           inst.inst_outputs = [ao] /\
           (case inst.inst_operands of Lit w :: _ => w2n w | _ => 0) = sz /\
           (?w. inst.inst_operands = [Lit w] /\ w2n w = sz)
Proof
  rw[m2v_promo_list_def, m2v_scan_def] >>
  drule m2v_promo_foldl_is_alloca >> simp[] >>
  strip_tac >> qexists `i` >> gvs[MEM_FILTER]
QED

(* ao from promo_list is NOT a fresh var *)
Theorem m2v_promo_list_ao_not_fresh:
  !fn ao pvar sz.
    m2v_fresh_names_disjoint fn /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    ao NOTIN m2v_fresh_vars fn
Proof
  rw[] >> drule m2v_promo_list_is_alloca >> strip_tac >>
  CCONTR_TAC >> gvs[m2v_fresh_names_disjoint_def] >>
  qpat_x_assum `!v. _` (qspecl_then [`ao`] mp_tac) >> simp[] >>
  qexists `inst` >> simp[]
QED

(* Each promo entry's alloca instruction has inst_id in m2v_promoted_ids *)
Theorem m2v_promo_list_inst_in_promoted_ids:
  !fn ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
           inst.inst_outputs = [ao] /\
           inst.inst_id IN m2v_promoted_ids fn
Proof
  rpt strip_tac >>
  drule m2v_promo_list_is_alloca >> strip_tac >>
  drule m2v_promo_list_can_promote >> strip_tac >>
  qexists `inst` >> simp[] >>
  rw[m2v_promoted_ids_def, GSPECIFICATION] >>
  qexists `inst` >> simp[]
QED

(* SSA uniqueness: if two instructions both output ao, they're equal *)
Theorem ssa_alloca_output_unique:
  !fn inst1 inst2 ao.
    ssa_form fn /\
    MEM inst1 (fn_insts fn) /\ MEM inst2 (fn_insts fn) /\
    MEM ao inst1.inst_outputs /\ MEM ao inst2.inst_outputs ==>
    inst1 = inst2
Proof
  metis_tac[all_distinct_flat_map_unique, ssa_form_def]
QED

Theorem fn_inst_wf_MEM:
  !fn inst. fn_inst_wf fn /\ MEM inst (fn_insts fn) ==> inst_wf inst
Proof
  rw[fn_inst_wf_def, fn_insts_def] >>
  drule mem_fn_insts_blocks_rev >> metis_tac[]
QED

(* General: ALL_DISTINCT on MAP FST means same key → same value *)
Theorem ALL_DISTINCT_MAP_FST_MEM_eq[local]:
  !l k v1 v2. ALL_DISTINCT (MAP FST l) /\
    MEM (k,v1) l /\ MEM (k,v2) l ==> v1 = v2
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP, FORALL_PROD] >> metis_tac[FST]
QED

(* FOLDL invariant: MAP FST of accumulated promos stays ALL_DISTINCT
   when input list has ALL_DISTINCT outputs and initial promos are disjoint *)
Theorem m2v_promo_foldl_fst_distinct[local]:
  !xs dfg ctr0 promos0 fresh0.
    ALL_DISTINCT (MAP FST promos0 ++ FLAT (MAP instruction_inst_outputs xs)) ==>
    ALL_DISTINCT (MAP FST
      (FST (SND (FOLDL (m2v_scan_step dfg) (ctr0,promos0,fresh0) xs))))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `m2v_scan_step dfg (ctr0,promos0,fresh0) h` >>
  Cases_on `r` >> simp[] >> first_x_assum irule >>
  gvs[m2v_scan_step_def, AllCaseEqs(), ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

(* General: ALL_DISTINCT of FLAT MAP is preserved under FILTER *)
Theorem ALL_DISTINCT_FLAT_MAP_FILTER[local]:
  !f P xs. ALL_DISTINCT (FLAT (MAP f xs)) ==>
    ALL_DISTINCT (FLAT (MAP f (FILTER P xs)))
Proof
  Induct_on `xs` >> simp[] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> res_tac >>
  fs[MEM_FILTER] >> metis_tac[]
QED

(* FOLDL invariant: every accumulated promo entry has pvar = m2v_fresh_var ao c *)
Theorem m2v_promo_foldl_pvar_fresh[local]:
  !xs dfg ctr0 promos0 fresh0.
    (!ao pvar sz. MEM (ao,pvar,sz) promos0 ==> ?c. pvar = m2v_fresh_var ao c) ==>
    !ao pvar sz. MEM (ao,pvar,sz)
      (FST (SND (FOLDL (m2v_scan_step dfg) (ctr0,promos0,fresh0) xs))) ==>
    ?c. pvar = m2v_fresh_var ao c
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `m2v_scan_step dfg (ctr0,promos0,fresh0) h` >>
  Cases_on `r` >> simp[] >>
  first_x_assum (qspecl_then [`dfg`,`q`,`q'`,`r''`] mp_tac) >>
  (impl_tac >- (gvs[m2v_scan_step_def, AllCaseEqs()] >> metis_tac[])) >>
  simp[]
QED

(* Top-level: promo list entries have pvar = m2v_fresh_var ao c *)
Theorem m2v_promo_list_pvar_is_fresh[local]:
  !fn ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==> ?c. pvar = m2v_fresh_var ao c
Proof
  rpt strip_tac >> fs[m2v_promo_list_def, m2v_scan_def] >>
  irule m2v_promo_foldl_pvar_fresh >>
  goal_assum (drule_at Any) >> simp[]
QED

(* SSA ==> MAP FST (m2v_promo_list fn) is ALL_DISTINCT *)
Theorem m2v_promo_list_fst_distinct[local]:
  !fn. ssa_form fn ==> ALL_DISTINCT (MAP FST (m2v_promo_list fn))
Proof
  rpt strip_tac >>
  simp[m2v_promo_list_def, m2v_scan_def] >>
  irule m2v_promo_foldl_fst_distinct >> simp[] >>
  fs[ssa_form_def] >>
  irule ALL_DISTINCT_FLAT_MAP_FILTER >>
  pop_assum mp_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

(* SSA: same ao in promo_list means same entry *)
Theorem m2v_promo_list_ao_unique:
  !fn ao pvar1 sz1 pvar2 sz2.
    ssa_form fn /\
    MEM (ao,pvar1,sz1) (m2v_promo_list fn) /\
    MEM (ao,pvar2,sz2) (m2v_promo_list fn) ==>
    pvar1 = pvar2 /\ sz1 = sz2
Proof
  rpt gen_tac >> strip_tac >>
  metis_tac[ALL_DISTINCT_MAP_FST_MEM_eq, m2v_promo_list_fst_distinct,
            PAIR, FST, SND, PAIR_EQ]
QED

(* String separator lemma: s1 ++ "_" ++ d1 = s2 ++ "_" ++ d2
   with no "_" in d1,d2 implies s1=s2, d1=d2 *)
Theorem strcat_sep_unique[local]:
  !(s1:string) d1 s2 d2.
    STRCAT s1 (STRING #"_" d1) = STRCAT s2 (STRING #"_" d2) /\
    ~MEM #"_" d1 /\ ~MEM #"_" d2 ==>
    s1 = s2 /\ d1 = d2
Proof
  Induct_on `s1`
  >- (rpt gen_tac >> Cases_on `s2` >> simp[])
  >> rpt gen_tac >> strip_tac >> Cases_on `s2` >> fs[]
  >- metis_tac[MEM_APPEND, MEM]
  >> first_x_assum (qspecl_then [`d1`,`t`,`d2`] mp_tac) >> fs[]
QED

(* toString produces no underscores *)
Theorem toString_no_underscore[local]:
  !n:num. ~MEM #"_" (toString n)
Proof
  strip_tac >> strip_tac >>
  mp_tac (Q.SPEC `n` EVERY_isDigit_num_to_dec_string) >>
  strip_tac >> fs[EVERY_MEM] >>
  first_x_assum drule >> EVAL_TAC
QED

(* m2v_fresh_var is fully injective *)
Theorem m2v_fresh_var_11:
  !ao1 c1 ao2 c2.
    m2v_fresh_var ao1 c1 = m2v_fresh_var ao2 c2 ==>
    ao1 = ao2 /\ c1 = c2
Proof
  rpt gen_tac >> simp[m2v_fresh_var_def, STRCAT_ASSOC] >> strip_tac >>
  `STRCAT ao1 (STRING #"_" (toString c1)) =
   STRCAT ao2 (STRING #"_" (toString c2))` by fs[] >>
  drule strcat_sep_unique >> simp[toString_no_underscore, toString_11]
QED

(* pvar uniqueness at the top level *)
Theorem m2v_promo_list_pvar_unique:
  !fn ao1 pvar sz1 ao2 sz2.
    ssa_form fn /\
    MEM (ao1,pvar,sz1) (m2v_promo_list fn) /\
    MEM (ao2,pvar,sz2) (m2v_promo_list fn) ==>
    (ao1,pvar,sz1) = (ao2,pvar,sz2)
Proof
  rpt strip_tac >>
  `?c1. pvar = m2v_fresh_var ao1 c1` by metis_tac[m2v_promo_list_pvar_is_fresh] >>
  `?c2. pvar = m2v_fresh_var ao2 c2` by metis_tac[m2v_promo_list_pvar_is_fresh] >>
  `ao1 = ao2 /\ c1 = c2` by metis_tac[m2v_fresh_var_11] >>
  gvs[] >>
  metis_tac[m2v_promo_list_ao_unique]
QED

(* Fresh var names don't appear as Var operands of original instructions *)
Theorem m2v_fresh_not_in_operands:
  !fn inst v.
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    v IN m2v_fresh_vars fn ==>
    ~MEM (Var v) inst.inst_operands
Proof
  rw[m2v_fresh_names_disjoint_def]
QED

(* Operand agreement: if states agree on non-fresh vars, labels,
   and the instruction is from the original function, all operands agree. *)
Theorem m2v_step_operand_agrees:
  !fn inst s1 s2 op.
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    (!v. v NOTIN m2v_fresh_vars fn ==>
         lookup_var v s1 = lookup_var v s2) /\
    s1.vs_labels = s2.vs_labels /\
    MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
  first_x_assum irule >>
  CCONTR_TAC >> gvs[] >>
  metis_tac[m2v_fresh_not_in_operands]
QED

(* Any step_inst preserves lookup_var for non-output variables. *)
Theorem step_inst_preserves_non_output:
  !fuel ctx inst s s' v.
    step_inst fuel ctx inst s = OK s' /\
    ~MEM v inst.inst_outputs ==>
    lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars]
  >> metis_tac[step_preserves_non_output_vars]
QED

(* Fresh undefinedness is preserved by every successful instruction step. *)
Theorem m2v_fresh_undef_preserved_step:
  !fn inst fuel ctx s s'.
    step_inst fuel ctx inst s = OK s' /\
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    m2v_fresh_undef fn s ==>
    m2v_fresh_undef fn s'
Proof
  rw[m2v_fresh_undef_def] >>
  `~MEM v inst.inst_outputs` by
    (fs[m2v_fresh_names_disjoint_def] >> metis_tac[]) >>
  drule_all step_inst_preserves_non_output >> simp[]
QED

(* exec_block on original function preserves fresh_undef *)
Theorem m2v_fresh_undef_preserved_block:
  !fuel ctx bb s s' fn.
    exec_block fuel ctx bb s = OK s' /\
    MEM bb fn.fn_blocks /\ m2v_fresh_names_disjoint fn /\
    m2v_fresh_undef fn s ==>
    m2v_fresh_undef fn s'
Proof
  rw[m2v_fresh_undef_def] >>
  `lookup_var v s' = lookup_var v s` suffices_by (rw[] >> metis_tac[]) >>
  irule exec_block_preserves_non_output_vars >>
  metis_tac[m2v_fresh_not_in_block_outputs]
QED

(* ===== Bridge preservation infrastructure ===== *)

(* Non-ALLOCA, non-INVOKE step_inst_base preserves vs_allocas.
   Re-proved here because the venomMemProofs version is [local]. *)
Theorem step_inst_base_ok_preserves_allocas:
  !inst (s:venom_state) s'.
    step_inst_base inst s = OK s' /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s`, `s'`]
    venomMemPropsTheory.step_inst_base_preserves_allocas) >>
  ASM_REWRITE_TAC[] >> simp[]
QED

(* Legacy direct proof retained below is unnecessary now that the shared
   memory-frame theorem is available. *)
(*
  fs[step_inst_base_def, AllCaseEqs()] >>
  gvs[AllCaseEqs(),
      exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def,
      exec_ext_call_def, exec_delegatecall_def,
      exec_create_def, extract_venom_result_def, exec_alloca_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, mcopy_def,
      revert_state_def, eval_operands_def, jump_to_def,
      lookup_var_def, FLOOKUP_UPDATE, halt_state_def, set_returndata_def]
QED
*)

(* Alloca bridge: relates lookup_var of alloca outputs to vs_allocas.
   Two clauses:
   1. Forward: lookup_var ao = SOME addr => FLOOKUP allocas = SOME (w2n addr, sz)
   2. Size consistency: FLOOKUP allocas = SOME (base, sz') => sz' = sz *)
(* Bridge holds when alloca outputs are undefined and allocas empty *)
Theorem alloca_bridge_undef:
  !fn s.
    s.vs_allocas = FEMPTY /\
    (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
       lookup_var ao s = NONE) ==>
    alloca_bridge fn s
Proof
  rw[alloca_bridge_def] >>
  first_x_assum (qspecl_then [`ao`, `pvar`, `sz`] mp_tac) >> simp[]
QED

(* Helper: extract clause 1 (forward) from bridge *)
Theorem alloca_bridge_entry:
  !fn inst ao pvar sz s addr.
    alloca_bridge fn s /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ao] /\
    lookup_var ao s = SOME addr ==>
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n addr, sz)
Proof
  rw[alloca_bridge_def] >> res_tac
QED

(* Helper: extract clause 2 (sz + reverse lookup) from bridge *)
Theorem alloca_bridge_entry_sz:
  !fn inst ao pvar sz s base sz'.
    alloca_bridge fn s /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ao] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base, sz') ==>
    sz' = sz /\
    ?addr. lookup_var ao s = SOME addr /\ w2n addr = base
Proof
  rw[alloca_bridge_def] >> res_tac >> simp[]
QED

(* Bridge preserved by step_inst for non-ALLOCA, non-INVOKE in SSA *)
Theorem alloca_bridge_step_non_alloca:
  !fn fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode <> ALLOCA /\
    inst.inst_opcode <> INVOKE /\
    ssa_form fn /\ MEM inst (fn_insts fn) /\
    alloca_bridge fn s ==>
    alloca_bridge fn s'
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by fs[step_inst_non_invoke] >>
  drule_all step_inst_base_ok_preserves_allocas >> strip_tac >>
  simp[alloca_bridge_def] >> rpt strip_tac >>
  rename1 `MEM (ao2,_,sz2) _` >>
  rename1 `MEM inst2 (fn_insts fn)`
  >- suspend "cl1"
  >> suspend "cl2"
QED

Resume alloca_bridge_step_non_alloca[cl1]:
  (* Clause 1: ao2 not in inst.inst_outputs by SSA, so lookup_var preserved *)
  mp_tac (Q.SPECL [`fn`,`inst`,`inst2`,`ao2`] ssa_alloca_output_unique) >>
  simp[] >> strip_tac >>
  `~MEM ao2 inst.inst_outputs` by (strip_tac >> res_tac >> fs[]) >>
  `lookup_var ao2 s' = lookup_var ao2 s` by
    metis_tac[step_inst_preserves_non_output] >>
  fs[] >>
  mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`addr`]
            alloca_bridge_entry) >> simp[]
QED

Resume alloca_bridge_step_non_alloca[cl2]:
  (* Clause 2: allocas unchanged + lookup_var preserved by SSA.
     RESUME_TAC splits sz'=sz and ∃addr subgoals. *)
  RESUME_TAC >>
  mp_tac (Q.SPECL [`fn`,`inst`,`inst2`,`ao2`] ssa_alloca_output_unique) >>
  simp[] >> strip_tac >>
  `~MEM ao2 inst.inst_outputs` by (strip_tac >> res_tac >> fs[]) >>
  `lookup_var ao2 s' = lookup_var ao2 s` by
    metis_tac[step_inst_preserves_non_output] >>
  mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`base'`,`sz'`]
            alloca_bridge_entry_sz) >> gvs[] >> metis_tac[]
QED

Finalise alloca_bridge_step_non_alloca

(*  Helper: sz from promo_list matches alloca inst operand *)
Theorem m2v_promo_list_sz_from_inst:
  !fn ao pvar sz inst.
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ao] /\ ssa_form fn ==>
    (case inst.inst_operands of
       [] => 0
     | Lit w::_ => w2n w
     | Var _::_ => 0
     | Label _::_ => 0) = sz
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`sz`] m2v_promo_list_is_alloca) >>
  simp[] >> strip_tac >>
  rename1 `MEM inst2 (fn_insts fn)` >>
  mp_tac (Q.SPECL [`fn`,`inst`,`inst2`,`ao`] ssa_alloca_output_unique) >>
  simp[]
QED

(* Helper: alloca base address < dimword when alloca_inv + next < dimword *)
Theorem alloca_base_lt_dimword:
  !s iid base sz.
    alloca_inv s /\ FLOOKUP s.vs_allocas iid = SOME (base,sz) /\
    s.vs_alloca_next < dimword (:256) ==>
    base < dimword (:256)
Proof
  rpt strip_tac >>
  gvs[alloca_inv_def, alloca_next_valid_def] >>
  rename1 `FLOOKUP _ _ = SOME (base1, _)` >>
  first_x_assum (qspecl_then [`iid`,`base1`,`sz`] mp_tac) >> simp[]
QED

(* Bridge preserved by ALLOCA instruction *)
Theorem alloca_bridge_step_alloca:
  !fn fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_opcode <> INVOKE /\
    ssa_form fn /\ wf_function fn /\ MEM inst (fn_insts fn) /\
    alloca_inv s /\
    s.vs_alloca_next < dimword (:256) /\
    alloca_bridge fn s ==>
    alloca_bridge fn s'
Proof
  rpt strip_tac >> simp[alloca_bridge_def] >> rpt strip_tac >>
  rename1 `MEM (ao2,_,sz2) _` >>
  rename1 `MEM inst2 (fn_insts fn)` >>
  gvs[step_inst_non_invoke, step_inst_base_def, is_alloca_op_def,
      exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  mp_tac (Q.SPECL [`fn`,`inst`,`inst2`,`ao2`] ssa_alloca_output_unique) >>
  simp[] >> strip_tac
  (* Order: NONE-fwd, SOME-fwd, NONE-sz, SOME-sz, NONE-rev, SOME-rev *)
  >- suspend "none_fwd"
  >- suspend "some_fwd"
  >- suspend "none_sz"
  >- suspend "some_sz"
  >- suspend "none_rev"
  >> suspend "some_rev"
QED

(* NONE case, forward: lookup_var → FLOOKUP *)
Resume alloca_bridge_step_alloca[none_fwd]:
  Cases_on `ao2 = out` >> gvs[]
  >- (mp_tac (Q.SPECL [`fn`,`ao2`,`pvar`,`sz2`,`inst`]
        m2v_promo_list_sz_from_inst) >> simp[])
  >> (`inst2 <> inst` by (strip_tac >> gvs[]) >>
      `inst2.inst_id <> inst.inst_id` by metis_tac[wf_fn_inst_id_inj] >>
      gvs[FLOOKUP_UPDATE] >>
      mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`addr`]
        alloca_bridge_entry) >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
QED

(* SOME case, forward: allocas unchanged, use old bridge *)
Resume alloca_bridge_step_alloca[some_fwd]:
  Cases_on `ao2 = out` >> gvs[]
  (* ao2=out: gvs reduces goal to offset<dimword ∧ sz=sz2 *)
  >- (conj_tac
      >- (mp_tac (Q.SPECL [`s`,`inst.inst_id`,`offset`,`sz`]
            alloca_base_lt_dimword) >> simp[])
      >> (mp_tac (Q.SPECL [`fn`,`inst`,`ao2`,`pvar`,`sz2`,`s`,`offset`,`sz`]
            alloca_bridge_entry_sz) >> simp[]))
  (* ao2≠out: lookup_var ao2 unchanged *)
  >> (mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`addr`]
        alloca_bridge_entry) >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
QED

(* NONE case, sz: updated allocas *)
Resume alloca_bridge_step_alloca[none_sz]:
  Cases_on `ao2 = out` >> gvs[]
  >- (mp_tac (Q.SPECL [`fn`,`ao2`,`pvar`,`sz2`,`inst`]
        m2v_promo_list_sz_from_inst) >> simp[])
  >> (`inst2 <> inst` by (strip_tac >> gvs[]) >>
      `inst2.inst_id <> inst.inst_id` by metis_tac[wf_fn_inst_id_inj] >>
      gvs[FLOOKUP_UPDATE] >>
      mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`base'`,`sz'`]
        alloca_bridge_entry_sz) >> gvs[])
QED

(* SOME case, sz: allocas unchanged, direct from old bridge *)
Resume alloca_bridge_step_alloca[some_sz]:
  mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`base'`,`sz'`]
    alloca_bridge_entry_sz) >> gvs[]
QED

(* NONE case, reverse: FLOOKUP → lookup_var *)
Resume alloca_bridge_step_alloca[none_rev]:
  Cases_on `ao2 = out`
  >- (gvs[] >>
      qexists `n2w (s.vs_alloca_next)` >>
      gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD])
  >> (gvs[] >>
      `inst2 <> inst` by (strip_tac >> gvs[]) >>
      `inst2.inst_id <> inst.inst_id` by metis_tac[wf_fn_inst_id_inj] >>
      gvs[] >>
      mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`base'`,`sz'`]
        alloca_bridge_entry_sz) >>
      simp[lookup_var_def] >> metis_tac[])
QED

(* SOME case, reverse: allocas unchanged, use old bridge *)
Resume alloca_bridge_step_alloca[some_rev]:
  Cases_on `ao2 = out`
  >- (`offset < dimword (:256)` by
        (mp_tac (Q.SPECL [`s`,`inst.inst_id`,`offset`,`sz`]
          alloca_base_lt_dimword) >> simp[]) >>
      gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD])
  >> (gvs[] >>
      mp_tac (Q.SPECL [`fn`,`inst2`,`ao2`,`pvar`,`sz2`,`s`,`base'`,`sz'`]
        alloca_bridge_entry_sz) >>
      simp[lookup_var_def] >> metis_tac[])
QED

Finalise alloca_bridge_step_alloca

(* Combined: bridge preserved by any step_inst in no-INVOKE SSA *)
Theorem alloca_bridge_step:
  !fn fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode <> INVOKE /\
    ssa_form fn /\ wf_function fn /\ MEM inst (fn_insts fn) /\
    alloca_inv s /\
    s.vs_alloca_next < dimword (:256) /\
    alloca_bridge fn s ==>
    alloca_bridge fn s'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- metis_tac[alloca_bridge_step_alloca]
  >> metis_tac[alloca_bridge_step_non_alloca]
QED


Triviality ptr_matches_var_inst_idx[simp]:
  ptr_matches_var p v (s with vs_inst_idx := n) = ptr_matches_var p v s
Proof
  Cases_on `p` >> rename1 `Ptr alloc moff` >>
  Cases_on `alloc` >> Cases_on `moff` >>
  simp[ptr_matches_var_def, venomStateTheory.lookup_var_def]
QED

Triviality vs_inst_idx_update_transparent[simp]:
  alloca_inv (s with vs_inst_idx := n) = alloca_inv s /\
  (s with vs_inst_idx := n).vs_alloca_next = s.vs_alloca_next /\
  alloca_bridge fn (s with vs_inst_idx := n) = alloca_bridge fn s /\
  m2v_fresh_undef fn (s with vs_inst_idx := n) = m2v_fresh_undef fn s /\
  bp_ptr_sound bp (s with vs_inst_idx := n) = bp_ptr_sound bp s /\
  bp_ptrs_bounded bp fn (s with vs_inst_idx := n) = bp_ptrs_bounded bp fn s
Proof
  simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       alloca_bridge_def, venomStateTheory.lookup_var_def,
       m2v_fresh_undef_def,
       bp_ptr_sound_def,
       bp_ptrs_bounded_def, memloc_within_alloca_def]
QED

(* Exported version without [simp] — for downstream theories *)
Theorem vs_inst_idx_update_transparent_export =
  vs_inst_idx_update_transparent
