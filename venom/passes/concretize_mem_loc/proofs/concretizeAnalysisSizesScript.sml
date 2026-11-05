Theory concretizeAnalysisSizes
Ancestors
  concretizeAnalysisSizeLookup concretizeAnalysisBoundary frameAllocationSizes
  concretizeMemLocDefs venomWf venomInst venomExecSemantics
  removeUnusedSsaProofs finite_map list pred_set

(* Include zero-size local sites; the analysis option function intentionally
   omits them. Values at other instruction IDs are harmless extra metadata. *)
Definition source_alloca_sizes_def:
  source_alloca_sizes fn =
    FUN_FMAP (\aid. get_alloca_size fn (Allocation aid))
      (IMAGE (\i. i.inst_id) (set (fn_insts fn)))
End

Theorem source_alloca_sizes_lookup:
  MEM inst (fn_insts fn) ==>
  FLOOKUP (source_alloca_sizes fn) inst.inst_id =
    SOME (get_alloca_size fn (Allocation inst.inst_id))
Proof
  strip_tac >> simp[source_alloca_sizes_def, FLOOKUP_FUN_FMAP] >>
  metis_tac[]
QED

Theorem source_alloca_sizes_literal:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = Lit n :: rest ==>
  FLOOKUP (source_alloca_sizes fn) inst.inst_id = SOME (w2n n)
Proof
  metis_tac[source_alloca_sizes_lookup, get_alloca_size_from_inst]
QED

Theorem context_alloca_size_local:
  ~EXISTS (\(a,p,sz). a = aid) imports ==>
  context_alloca_size fn imports aid = get_alloca_size fn aid
Proof
  Induct_on `imports`
  >- simp[context_alloca_size_def, FIND_thm] >>
  gen_tac >> PairCases_on `h` >>
  gvs[context_alloca_size_def, FIND_thm]
QED

Theorem context_alloca_size_literal:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = Lit n :: rest /\
  ~EXISTS (\(a,p,sz). a = Allocation inst.inst_id) imports ==>
  context_alloca_size fn imports (Allocation inst.inst_id) = w2n n
Proof
  metis_tac[context_alloca_size_local, get_alloca_size_from_inst]
QED

Theorem context_alloca_size_option_literal:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = Lit n :: rest /\
  ~EXISTS (\(a,p,sz). a = Allocation inst.inst_id) imports ==>
  (if context_alloca_size fn imports (Allocation inst.inst_id) = 0 then NONE
   else SOME (context_alloca_size fn imports (Allocation inst.inst_id))) =
  (if w2n n = 0 then NONE else SOME (w2n n))
Proof
  strip_tac >> drule_all context_alloca_size_literal >> simp[]
QED

Theorem source_alloca_sizes_empty:
  s.vs_allocas = FEMPTY ==> cache_sizes_ok (source_alloca_sizes fn) s
Proof
  simp[cache_sizes_ok_empty]
QED

Theorem source_alloca_sizes_callee:
  setup_callee fn args caller = SOME callee ==>
  cache_sizes_ok (source_alloca_sizes fn) callee
Proof
  metis_tac[setup_callee_empty_allocas, source_alloca_sizes_empty]
QED

Theorem source_alloca_sizes_step:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  cache_sizes_ok (source_alloca_sizes fn) s /\
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode <> INVOKE ==>
  cache_sizes_ok (source_alloca_sizes fn) s'
Proof
  strip_tac >> irule cache_sizes_ok_step >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s`] >> simp[] >> strip_tac >>
  `?n. inst.inst_operands = [Lit n]` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat,
         EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     `inst_wf inst` by metis_tac[] >> gvs[inst_wf_def]) >>
  qexistsl_tac [`n`, `[]`] >> simp[] >>
  metis_tac[source_alloca_sizes_literal]
QED

Theorem cached_context_alloca_size:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\
  ~EXISTS (\(a,p,sz). a = Allocation inst.inst_id) imports /\
  cache_sizes_ok (source_alloca_sizes fn) s /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (if context_alloca_size fn imports (Allocation inst.inst_id) = 0 then NONE
   else SOME (context_alloca_size fn imports (Allocation inst.inst_id))) = SOME psz ==>
  sz = psz
Proof
  strip_tac >> drule_all cache_sizes_ok_lookup >>
  drule source_alloca_sizes_lookup >>
  drule context_alloca_size_local >>
  disch_then (qspec_then `fn` assume_tac) >> rpt strip_tac >> gvs[]
QED

Theorem source_zero_size_probe[local]:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 0w] /\
  ~EXISTS (\(a,p,sz). a = Allocation inst.inst_id) imports ==>
  FLOOKUP (source_alloca_sizes fn) inst.inst_id = SOME 0 /\
  (if context_alloca_size fn imports (Allocation inst.inst_id) = 0 then NONE
   else SOME (context_alloca_size fn imports (Allocation inst.inst_id))) = NONE
Proof
  strip_tac >> conj_tac
  >- (drule_all source_alloca_sizes_literal >> simp[]) >>
  drule_all context_alloca_size_option_literal >> simp[]
QED
