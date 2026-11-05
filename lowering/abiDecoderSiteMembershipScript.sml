(* Actual decoder sites must belong to the running function, not old blocks. *)
Theory abiDecoderSiteMembership
Ancestors
  abiDecoderSiteResources abiDecoderCode fragExec exprLoweringProps
  compileEnv list rich_list compilerOccurrences pred_set arithmetic

Theorem abi_decoder_new_code_fn_member:
  cs_extends first last /\ fn_has_code first last func /\
  abi_decoder_code_member i last /\
  (!bb. MEM bb first.cs_blocks ==> ~MEM i bb.bb_instructions) ==>
  MEM i (fn_insts func)
Proof
  strip_tac >>
  gvs[cs_extends_def, fn_has_code_def, abi_decoder_code_member_def,
      IS_PREFIX_APPEND]
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      simp[MEM_APPEND])
  >> `emitted_blocks first last = new` by
    metis_tac[emitted_blocks_append] >>
  metis_tac[lookup_block_fn_insts]
QED

Theorem abi_decoder_sites_fn_witness:
  cs_extends first last /\ fn_has_code first last func /\
  abi_decoder_code first last /\ abi_decoder_code_ids_below first /\
  id IN abi_decoder_sites first.cs_next_id last.cs_next_id last ==>
  ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
      i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]
Proof
  simp[abi_decoder_sites_member] >> strip_tac >>
  `~abi_decoder_code_member i first` by
    (gvs[abi_decoder_code_ids_below_def] >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  `MEM i (fn_insts func)` by
    (irule abi_decoder_new_code_fn_member >>
     qexistsl_tac [`first`, `last`] >> simp[] >>
     gvs[abi_decoder_code_member_def] >> metis_tac[]) >>
  drule_all abi_decoder_code_alloca >> strip_tac >>
  qexists_tac `i` >> simp[]
QED

Theorem compiler_emitted_blocks_member:
  last.cs_blocks = new ++ first.cs_blocks /\
  MEM i (compiler_emitted first last) ==>
  MEM i last.cs_current_insts \/
  ?bb. MEM bb new /\ MEM i bb.bb_instructions
Proof
  strip_tac >>
  qpat_x_assum `MEM i _` mp_tac >>
  simp[compiler_emitted_def, compiler_chrono_def, REVERSE_APPEND,
       MAP_APPEND, FLAT_APPEND, LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> strip_tac >>
  drule MEM_DROP_IMP >> simp[MEM_APPEND, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  metis_tac[]
QED

Theorem compiler_emitted_fn_member:
  cs_extends first last /\ fn_has_code first last func /\
  MEM i (compiler_emitted first last) ==>
  MEM i (fn_insts func)
Proof
  strip_tac >>
  qpat_x_assum `cs_extends _ _` (strip_assume_tac o REWRITE_RULE[cs_extends_def]) >>
  drule_all compiler_emitted_blocks_member >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND]
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      simp[MEM_APPEND]) >>
  `emitted_blocks first last = new` by metis_tac[emitted_blocks_append] >>
  metis_tac[lookup_block_fn_insts]
QED

Definition abi_decoder_emitted_sites_def:
  abi_decoder_emitted_sites lo hi first last =
    {id | lo <= id /\ id < hi /\
      ?i. MEM i (compiler_emitted first last) /\
          i.inst_id = id /\ i.inst_opcode = ALLOCA}
End

Theorem abi_decoder_emitted_sites_member[simp]:
  id IN abi_decoder_emitted_sites lo hi first last <=>
  lo <= id /\ id < hi /\
  ?i. MEM i (compiler_emitted first last) /\
      i.inst_id = id /\ i.inst_opcode = ALLOCA
Proof
  simp[abi_decoder_emitted_sites_def]
QED

Theorem abi_decoder_emitted_sites_finite[simp]:
  FINITE (abi_decoder_emitted_sites lo hi first last)
Proof
  irule SUBSET_FINITE_I >> qexists_tac `count hi` >> simp[SUBSET_DEF]
QED

Theorem abi_decoder_emitted_sites_split:
  lo <= mid /\ mid <= hi ==>
  abi_decoder_emitted_sites lo hi first last =
    abi_decoder_emitted_sites lo mid first last UNION
    abi_decoder_emitted_sites mid hi first last
Proof
  strip_tac >> simp[EXTENSION] >> gen_tac >>
  Cases_on `x < mid` >> simp[] >> decide_tac
QED

Theorem abi_decoder_emitted_sites_disjoint:
  DISJOINT (abi_decoder_emitted_sites lo mid first last)
           (abi_decoder_emitted_sites mid hi first last)
Proof
  simp[DISJOINT_DEF, EXTENSION] >>
  metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_ANTISYM]
QED

Theorem abi_decoder_emitted_sites_outside:
  id < lo \/ hi <= id ==>
  id NOTIN abi_decoder_emitted_sites lo hi first last
Proof
  simp[] >> metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_ANTISYM]
QED

Theorem abi_decoder_emitted_sites_fn_witness:
  cs_extends first last /\ fn_has_code first last func /\
  compiler_emits abi_decoder_alloc_shape first last /\
  id IN abi_decoder_emitted_sites lo hi first last ==>
  ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
      i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w] /\
      ?out. i.inst_outputs = [out]
Proof
  simp[] >> strip_tac >>
  drule compiler_emits_suffix >> strip_tac >>
  gvs[EVERY_MEM] >>
  `abi_decoder_alloc_shape i` by metis_tac[] >>
  `MEM i (fn_insts func)` by metis_tac[compiler_emitted_fn_member] >>
  qexists_tac `i` >> gvs[abi_decoder_alloc_shape_def]
QED

Theorem abi_decoder_emitted_sites_subinterval:
  lo <= a /\ b <= hi ==>
  abi_decoder_emitted_sites a b first last SUBSET
    abi_decoder_emitted_sites lo hi first last
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >> simp[]
QED

Theorem abi_decoder_emitted_sites_child:
  compiler_emits shape first child /\ compiler_emits shape child child_end /\
  compiler_emits shape child_end last ==>
  abi_decoder_emitted_sites lo hi child child_end SUBSET
    abi_decoder_emitted_sites lo hi first last
Proof
  strip_tac >>
  `compiler_emits shape first child_end` by metis_tac[compiler_emits_trans] >>
  `compiler_emitted first last =
     compiler_emitted first child_end ++ compiler_emitted child_end last` by
    metis_tac[compiler_emits_emitted_concat] >>
  `compiler_emitted first child_end =
     compiler_emitted first child ++ compiler_emitted child child_end` by
    metis_tac[compiler_emits_emitted_concat] >>
  simp[SUBSET_DEF] >> metis_tac[MEM_APPEND]
QED

Theorem abi_decoder_emitted_sites_subsegment:
  cs_extends first child /\ cs_extends child child_end /\ cs_extends child_end last /\
  first.cs_next_id <= child.cs_next_id /\ child_end.cs_next_id <= last.cs_next_id ==>
  abi_decoder_emitted_sites child.cs_next_id child_end.cs_next_id child child_end SUBSET
    abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >>
  `MEM i (compiler_emitted first last)` by
    (irule compiler_emitted_subsegment >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem abi_decoder_emitted_alloca:
  compiler_emits abi_decoder_alloc_shape first last /\
  MEM inst (compiler_emitted first last) /\ inst.inst_opcode = ALLOCA ==>
  first.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id /\
  inst.inst_operands = [Lit 32w] /\ ?out. inst.inst_outputs = [out]
Proof
  strip_tac >> drule compiler_emits_suffix >> simp[EVERY_MEM] >>
  strip_tac >> `abi_decoder_alloc_shape inst` by metis_tac[] >>
  gvs[abi_decoder_alloc_shape_def] >> metis_tac[]
QED

Theorem abi_decoder_emitted_site_generated_allocation:
  compiler_emits abi_decoder_alloc_shape first last /\
  MEM inst (compiler_emitted first last) /\ inst.inst_opcode = ALLOCA /\
  abi_decoder_site_budget ids cap s /\
  abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last SUBSET ids ==>
  ?out t p base len. inst.inst_outputs = [out] /\
    inst.inst_operands = [Lit 32w] /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_site_budget ids cap t /\ lookup_var out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    MEM (base,len) (abi_decoder_child_scratch
      (abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last)
      0 cap s) /\ base <= p /\ p + 32 <= base + len
Proof
  strip_tac >> drule_all abi_decoder_emitted_alloca >> strip_tac >>
  `inst.inst_id IN abi_decoder_emitted_sites
     first.cs_next_id last.cs_next_id first last` by
    (simp[] >> metis_tac[]) >>
  qpat_x_assum `compiler_emits _ _ _` kall_tac >>
  qpat_x_assum `MEM inst _` kall_tac >>
  metis_tac[abi_decoder_site_allocation]
QED
