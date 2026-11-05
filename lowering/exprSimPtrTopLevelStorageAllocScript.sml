(* Allocation interface probes for storage/transient aggregate forcing. *)
Theory exprSimPtrTopLevelStorageAlloc
Ancestors
  allocationPtr exprSimStorageCopy exprSimAlloc exprSimHyps valueEncodingProps
  exprSimHypsDefs exprLoweringProps bodyPtrDefs context compileEnv vyperAST
  venomInst venomState venomExecSemantics ptrDiscipline words finite_map

Theorem toplevel_storage_fresh_alloca_coverage:
  FLOOKUP s.vs_allocas id = NONE /\
  s.vs_alloca_next + nb < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK s1 ==>
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s s1 tn) out s1 nb
Proof
  metis_tac[fresh_alloca_ptr_covers]
QED

Theorem toplevel_storage_reused_alloca_coverage:
  FLOOKUP s.vs_allocas id = SOME (b,nb) /\ b+nb < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK s1 ==>
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s s1 tn) out s1 nb
Proof
  strip_tac >> drule reused_alloca_step >>
  disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  irule (cj 1 reused_alloca_ptr_covers) >> simp[]
QED

Theorem toplevel_storage_copy_capacity:
  expr_body_pre cenv cx env (TopLevelName ann nsid) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann ==>
  type_memory_bytes cenv ann = 32 * type_slot_size tv /\
  type_memory_bytes cenv ann < 2**64
Proof
  strip_tac >> drule expr_body_pre_copy_ok >>
  simp[expr_type_def, type_memory_size_slots]
QED

(* The ordinary allocation execution boundary re-establishes stmt_state_rel;
   this extracts all loop arithmetic premises without requiring freshness. *)
Theorem toplevel_storage_allocated_bounds:
  expr_body_pre cenv cx env (TopLevelName ann nsid) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann /\
  nb = type_memory_bytes cenv ann /\
  stmt_state_rel ctx func cenv cx es s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,nb) ==>
  nb = 32 * type_slot_size tv /\ type_slot_size tv < 2**256 /\
  b + 32 * type_slot_size tv < 2**256 /\
  b + 32 * type_slot_size tv <= s1.vs_alloca_next
Proof
  strip_tac >> drule_all toplevel_storage_copy_capacity >> strip_tac >>
  `alloca_room ctx func s1 /\ alloca_inv s1` by
    fs[stmt_state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  `b+nb <= s1.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  gvs[dimword_def] >> decide_tac
QED

Theorem toplevel_storage_copy_word_count:
  expr_body_pre cenv cx env (TopLevelName ann nsid) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann ==>
  (type_memory_bytes cenv ann + 31) DIV 32 = type_slot_size tv /\
  type_memory_bytes cenv ann < dimword (:256)
Proof
  strip_tac >> drule_all toplevel_storage_copy_capacity >> strip_tac >>
  gvs[dimword_def] >> decide_tac
QED
