(* Concrete function sites and public resource premises for the shared spine. *)
Theory abiEncoderSharedWindowAdapter
Ancestors
  abiEncoderSharedContract abiEncoderProps abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry exprLoweringProps venomMemDefs venomState
  compileEnv venomInst venomWf localPtrsProps valueEncoding finite_map pred_set list arithmetic words

Definition abi_encoder_alloca_sites_def:
  abi_encoder_alloca_sites func =
    {id | ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit 32w] /\ id = inst.inst_id}
End

Theorem abi_encoder_alloca_sites_cover:
  abi_sites_cover func (abi_encoder_alloca_sites func)
Proof
  simp[abi_sites_cover_def, abi_encoder_alloca_sites_def] >> metis_tac[]
QED

Theorem abi_encoder_literal32_charge[local]:
  !insts P.
    32 * LENGTH (FILTER (\i:instruction. P i /\ i.inst_operands = [Lit 32w]) insts) <=
    SUM (MAP alloca_lit_size (FILTER P insts))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `P h` >> simp[] >>
  Cases_on `h.inst_operands = [Lit 32w]` >> simp[] >>
  gvs[alloca_lit_size_def] >> first_x_assum (qspec_then `P` mp_tac) >> simp[dimword_def]
QED

Theorem abi_encoder_alloca_missing_charge:
  32 * CARD (abi_sites_decoder_missing (abi_encoder_alloca_sites func) first last s) <=
  pending_alloca_size func s
Proof
  qabbrev_tac `pending = FILTER (\i:instruction. i.inst_opcode = ALLOCA /\
    i.inst_id NOTIN FDOM s.vs_allocas /\ i.inst_operands = [Lit 32w]) (fn_insts func)` >>
  `abi_sites_decoder_missing (abi_encoder_alloca_sites func) first last s SUBSET
    set (MAP (\i. i.inst_id) pending)` by
    (simp[abi_sites_decoder_missing_def, abi_sites_decoder_ids_def,
       abi_encoder_alloca_sites_def, SUBSET_DEF, MEM_MAP, MEM_FILTER, Abbr `pending`] >>
     metis_tac[]) >>
  `CARD (abi_sites_decoder_missing (abi_encoder_alloca_sites func) first last s) <=
    LENGTH pending` by
    (irule LESS_EQ_TRANS >> qexists_tac `CARD (set (MAP (\i. i.inst_id) pending))` >>
     conj_tac >- (irule CARD_SUBSET >> simp[]) >>
     metis_tac[CARD_LIST_TO_SET, LENGTH_MAP]) >>
  `32 * LENGTH pending <= pending_alloca_size func s` by
    (mp_tac (Q.SPECL [`fn_insts func`,
       `\i:instruction. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN FDOM s.vs_allocas`]
      abi_encoder_literal32_charge) >>
     simp[pending_alloca_size_def, Abbr `pending`, GSYM CONJ_ASSOC]) >>
  decide_tac
QED

Theorem abi_encoder_alloca_sites_fragment:
  i IN abi_sites_decoder_ids (abi_encoder_alloca_sites func)
    st.cs_next_id st'.cs_next_id ==>
  i IN frag_ids st st' /\
  ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = i
Proof
  simp[abi_sites_decoder_ids_def, abi_encoder_alloca_sites_def, frag_ids_def] >>
  metis_tac[]
QED

Theorem abi_encoder_alloca_window_budget:
  alloca_inv s /\ alloca_room ctx func s /\
  (!inst off sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz) ==>
    sz = 32) ==>
  abi_sites_decoder_budget (abi_encoder_alloca_sites func)
    st.cs_next_id st'.cs_next_id 0
    (s.vs_alloca_next + 32 * CARD (abi_sites_decoder_missing
      (abi_encoder_alloca_sites func) st.cs_next_id st'.cs_next_id s)) s
Proof
  strip_tac >>
  mp_tac (Q.INST [`first` |-> `st.cs_next_id`, `last` |-> `st'.cs_next_id`]
    abi_encoder_alloca_missing_charge) >> strip_tac >>
  `s.vs_alloca_next + 32 * CARD (abi_sites_decoder_missing
     (abi_encoder_alloca_sites func) st.cs_next_id st'.cs_next_id s) < dimword (:256)` by
    (qpat_x_assum `alloca_room ctx func s` mp_tac >>
     pure_rewrite_tac[alloca_room_def] >> strip_tac >> decide_tac) >>
  pure_rewrite_tac[abi_sites_decoder_budget_def] >>
  simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ZERO_LESS_EQ,
    arithmeticTheory.LESS_EQ_REFL] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `alloca_inv s` mp_tac >>
  pure_rewrite_tac[alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> drule abi_encoder_alloca_sites_fragment >> strip_tac >>
      `sz = 32` by metis_tac[] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem abi_encoder_alloca_window_disjoint:
  s.vs_alloca_next <= top /\ p+n <= s.vs_alloca_next /\ n <> 0 /\
  (!inst off sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (p,n) (off,sz)) ==>
  abi_footprint_disjoint p n
    (abi_decoder_child_scratch (abi_sites_decoder_ids (abi_encoder_alloca_sites func)
      st.cs_next_id st'.cs_next_id) 0 top s)
Proof
  strip_tac >> irule abi_decoder_child_scratch_disjoint >> simp[] >>
  rpt strip_tac >> drule abi_encoder_alloca_sites_fragment >> strip_tac >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (p,n) (q,sz)` by metis_tac[] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p,n) (q,sz)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def, pairTheory.FST,
    pairTheory.SND] >> decide_tac
QED

Theorem abi_encoder_positive_window_input:
  abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  sb + source_cap <= initial.vs_alloca_next /\
  d + LENGTH (enc at av) <= initial.vs_alloca_next /\
  initial.vs_alloca_next <= top /\ top < dimword (:256) /\
  LENGTH (enc at av) <> 0 /\
  venomMemDefs$regions_disjoint (sb,source_cap) (d,LENGTH (enc at av)) /\
  (!inst off sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (off,sz) ==>
    sz = 32 /\
    venomMemDefs$regions_disjoint (sb,source_cap) (off,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (off,sz)) ==>
  abi_sites_encoder_shared_input (abi_encoder_alloca_sites func)
    (ei,at,av) (st,src,dst) (sb,source_cap) (d,LENGTH (enc at av))
    (st.cs_next_id,st'.cs_next_id,0,top)
    (abi_decoder_prune_vars st.cs_next_var initial)
Proof
  strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    (qpat_x_assum `!x. src = Var x \/ dst = Var x ==> _` mp_tac >>
     Cases_on `src` >> Cases_on `dst` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> metis_tac[]) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w d)` by
    metis_tac[abi_decoder_prune_eval] >>
  `(source_cap <> 0 ==> abi_footprint_disjoint sb source_cap
     (abi_decoder_child_scratch (abi_sites_decoder_ids (abi_encoder_alloca_sites func)
       st.cs_next_id st'.cs_next_id) 0 top initial)) /\
    abi_footprint_disjoint d (LENGTH (enc at av))
     (abi_decoder_child_scratch (abi_sites_decoder_ids (abi_encoder_alloca_sites func)
       st.cs_next_id st'.cs_next_id) 0 top initial)` by
    (conj_tac
     >- (strip_tac >> irule abi_encoder_alloca_window_disjoint >>
         asm_rewrite_tac[] >> metis_tac[]) >>
     irule abi_encoder_alloca_window_disjoint >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  simp_tac bool_ss [abi_sites_encoder_shared_input_def] >>
  asm_rewrite_tac[] >>
  fs[abi_decoder_prune_vars_def, abi_decoder_child_scratch_def]
QED

(* Split a pending sum, counting the constant-weight selected entries. *)
Theorem abi_encoder_charge_split[local]:
  !ls P Q f c.
    (!i. MEM i ls /\ P i /\ Q i ==> f i = c) ==>
    SUM (MAP f (FILTER P ls)) =
      c * LENGTH (FILTER (\i. P i /\ Q i) ls) +
      SUM (MAP f (FILTER (\i. P i /\ ~Q i) ls))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`P`, `Q`, `f`, `c`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  Cases_on `P h` >> Cases_on `Q h` >> simp[] >>
  `f h = c` by metis_tac[] >> simp[MULT_SUC]
QED

Theorem abi_encoder_alloca_pending_partition:
  fn_inst_ids_distinct func ==>
  pending_alloca_size func s =
    32 * CARD (abi_sites_decoder_missing (abi_encoder_alloca_sites func) first last s) +
    SUM (MAP alloca_lit_size
      (FILTER (\inst. inst.inst_opcode = ALLOCA /\
        inst.inst_id NOTIN FDOM s.vs_allocas /\
        inst.inst_id NOTIN abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last)
        (fn_insts func)))
Proof
  strip_tac >>
  qabbrev_tac `ids = abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last` >>
  qabbrev_tac `pending = FILTER (\i:instruction. i.inst_opcode = ALLOCA /\
    i.inst_id NOTIN FDOM s.vs_allocas /\ i.inst_id IN ids) (fn_insts func)` >>
  `!i. MEM i (fn_insts func) /\ i.inst_id IN ids ==>
       i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]` by
    (simp[Abbr `ids`, abi_sites_decoder_ids_def, abi_encoder_alloca_sites_def] >>
     rpt strip_tac >>
     `i = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
  `set (MAP (\i:instruction. i.inst_id) pending) =
    abi_sites_decoder_missing (abi_encoder_alloca_sites func) first last s` by
    (simp[EXTENSION, MEM_MAP, MEM_FILTER, Abbr `pending`, Abbr `ids`,
      abi_sites_decoder_missing_def, abi_sites_decoder_ids_def, abi_encoder_alloca_sites_def] >>
     metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i:instruction. i.inst_id) (fn_insts func))` by
    (`!bbs. MAP (\i:instruction. i.inst_id) (fn_insts_blocks bbs) =
       FLAT (MAP (\bb. MAP (\i:instruction. i.inst_id) bb.bb_instructions) bbs)` by
       (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
     fs[fn_inst_ids_distinct_def, fn_insts_def]) >>
  `ALL_DISTINCT (MAP (\i:instruction. i.inst_id) pending)` by
    (irule ALL_DISTINCT_MAP_INJ >> conj_tac
     >- (simp[Abbr `pending`, MEM_FILTER] >> metis_tac[fn_inst_ids_distinct_inj]) >>
     unabbrev_all_tac >> irule FILTER_ALL_DISTINCT >> metis_tac[ALL_DISTINCT_MAP]) >>
  `CARD (abi_sites_decoder_missing (abi_encoder_alloca_sites func) first last s) =
    LENGTH pending` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET, LENGTH_MAP] >>
  mp_tac (Q.ISPECL [`fn_insts func`,
    `\i:instruction. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN FDOM s.vs_allocas`,
    `\i:instruction. i.inst_id IN ids`, `alloca_lit_size`, `32`] abi_encoder_charge_split) >>
  (impl_tac >- (rpt strip_tac >> fs[] >> first_x_assum drule_all >>
     simp[alloca_lit_size_def, dimword_def])) >>
  simp[pending_alloca_size_def, Abbr `pending`, GSYM CONJ_ASSOC]
QED

Theorem abi_encoder_alloca_room_from_budget:
  fn_inst_ids_distinct func /\ alloca_room ctx func s /\
  abi_encoder_registered_effect
    (abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last) outs s t /\
  abi_sites_decoder_budget (abi_encoder_alloca_sites func) first last 0
    (s.vs_alloca_next + 32 * CARD (abi_sites_decoder_missing
      (abi_encoder_alloca_sites func) first last s)) t ==>
  alloca_room ctx func t
Proof
  strip_tac >>
  `!i. i NOTIN abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last ==>
    FLOOKUP t.vs_allocas i = FLOOKUP s.vs_allocas i` by
    (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     simp_tac bool_ss [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `FILTER (\inst:instruction. inst.inst_opcode = ALLOCA /\
        inst.inst_id NOTIN FDOM t.vs_allocas /\
        inst.inst_id NOTIN abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last)
        (fn_insts func) =
   FILTER (\inst:instruction. inst.inst_opcode = ALLOCA /\
        inst.inst_id NOTIN FDOM s.vs_allocas /\
        inst.inst_id NOTIN abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last)
        (fn_insts func)` by
    (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> gen_tac >>
     Cases_on `inst.inst_id IN abi_sites_decoder_ids (abi_encoder_alloca_sites func) first last`
     >- simp[] >>
     first_x_assum drule >> simp[FLOOKUP_DEF] >>
     Cases_on `inst.inst_id IN FDOM t.vs_allocas` >>
     Cases_on `inst.inst_id IN FDOM s.vs_allocas` >> simp[]) >>
  drule abi_encoder_alloca_pending_partition >>
  disch_then (qspecl_then [`s`, `last`, `first`] assume_tac) >>
  drule abi_encoder_alloca_pending_partition >>
  disch_then (qspecl_then [`t`, `last`, `first`] assume_tac) >>
  qpat_x_assum `abi_sites_decoder_budget _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_sites_decoder_budget_def] >> strip_tac >>
  qpat_x_assum `alloca_room ctx func s` mp_tac >>
  pure_rewrite_tac[alloca_room_def] >> strip_tac >>
  simp_tac bool_ss [alloca_room_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  qpat_x_assum `abi_encoder_registered_effect _ _ _ _` kall_tac >>
  qpat_x_assum `!i. _ ==> FLOOKUP _ _ = FLOOKUP _ _` kall_tac >>
  qpat_x_assum `!i j p q. _` kall_tac >>
  qpat_x_assum `!id off sz. _` kall_tac >>
  full_simp_tac bool_ss [] >> decide_tac
QED
