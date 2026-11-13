Theory exprSimAbiEncodeChargeTransfer
Ancestors
  exprSimAbiEncodeResources exprLoweringProps venomWf venomInst venomState
  finite_map list rich_list words

Theorem abi_encode_sum_difference[local]:
  !ys xs (f:'a -> num) g.
    ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
    (!x. MEM x ys ==> MEM x xs) /\
    (!x. MEM x xs /\ ~MEM x ys ==> f x = g x) ==>
    SUM (MAP f xs) + SUM (MAP g ys) =
    SUM (MAP g xs) + SUM (MAP f ys)
Proof
  Induct_on `ys`
  >- (simp[] >> rpt strip_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[]) >>
  rpt gen_tac >> simp[ALL_DISTINCT] >> strip_tac >>
  `MEM h xs` by metis_tac[] >>
  qpat_x_assum `MEM h xs` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspecl_then [`l1 ++ l2`, `f`, `g`] mp_tac) >>
  impl_tac
  >- (simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  simp[MAP_APPEND, SUM_APPEND] >> decide_tac
QED

Theorem abi_encode_sum_filter[local]:
  !xs (p:'a -> bool) w.
    SUM (MAP w (FILTER p xs)) = SUM (MAP (\x. if p x then w x else 0) xs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `p h` >> simp[]
QED

Theorem abi_encode_pending_weight[local]:
  pending_alloca_size func s =
  SUM (MAP (\i. if i.inst_id NOTIN FDOM s.vs_allocas then alloca_lit_size i else 0)
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)))
Proof
  rewrite_tac[pending_alloca_size_def, GSYM FILTER_FILTER, abi_encode_sum_filter] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
  Cases_on `x.inst_opcode = ALLOCA` >> simp[]
QED

Theorem abi_encode_insts_distinct[local]:
  fn_inst_ids_distinct func ==> ALL_DISTINCT (fn_insts func)
Proof
  `!bbs. MAP (\j. j.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
    fs[fn_inst_ids_distinct_def, fn_insts_def] >>
  metis_tac[ALL_DISTINCT_MAP]
QED

Theorem abi_encode_pending_difference:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
       ~MEM i (fn_insts obs) ==>
       FLOOKUP t.vs_allocas i.inst_id = FLOOKUP s.vs_allocas i.inst_id) ==>
  pending_alloca_size func t + pending_alloca_size obs s =
  pending_alloca_size func s + pending_alloca_size obs t
Proof
  strip_tac >> rewrite_tac[abi_encode_pending_weight] >>
  irule abi_encode_sum_difference >>
  conj_tac
  >- (simp[MEM_FILTER] >> rpt strip_tac >>
      `FLOOKUP t.vs_allocas x.inst_id = FLOOKUP s.vs_allocas x.inst_id` by metis_tac[] >>
      `x.inst_id IN FDOM t.vs_allocas <=> x.inst_id IN FDOM s.vs_allocas` by
        metis_tac[flookup_thm] >> simp[]) >>
  conj_tac >- (simp[MEM_FILTER] >> metis_tac[]) >>
  conj_tac >> irule FILTER_ALL_DISTINCT >> metis_tac[abi_encode_insts_distinct]
QED

Theorem abi_encode_charge_difference_lift:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
       ~MEM i (fn_insts obs) ==>
       FLOOKUP t.vs_allocas i.inst_id = FLOOKUP s.vs_allocas i.inst_id) /\
  t.vs_alloca_next + pending_alloca_size obs t <=
    s.vs_alloca_next + pending_alloca_size obs s ==>
  t.vs_alloca_next + pending_alloca_size func t <=
    s.vs_alloca_next + pending_alloca_size func s
Proof
  strip_tac >> drule_all abi_encode_pending_difference >> decide_tac
QED
