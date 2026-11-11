Theory bodyIntCallRuntimeChargePackaging
Ancestors
  vyperCompiler loweringShapeDefs venomInst list passSimulationProofs

(* Successful splitting retains the delimiter and every block. *)
Theorem split_blocks_at_partition:
  !blocks label prefix suffix.
    split_blocks_at label blocks = SOME (prefix,suffix) ==>
    blocks = prefix ++ suffix
Proof
  Induct_on `blocks` >> simp[split_blocks_at_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem package_internal_blocks_partition:
  !descriptors blocks entry functions.
    package_internal_blocks descriptors blocks = SOME (entry,functions) ==>
    blocks = entry ++ FLAT (MAP (\fn. fn.fn_blocks) functions)
Proof
  Induct_on `descriptors`
  >- simp[package_internal_blocks_def] >>
  rpt gen_tac >> rename1 `package_internal_blocks (descriptor :: _) _` >>
  PairCases_on `descriptor` >>
  simp[package_internal_blocks_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule split_blocks_at_partition >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[mk_internal_function_metadata, APPEND_ASSOC]
QED

(* Extraction is an ordered, multiplicity-preserving view of the state. *)
Theorem extract_context_with_internals_insts:
  !entry_label internal_fns st ctx data.
    extract_context_with_internals entry_label internal_fns st =
      SOME (ctx,data) ==>
    FLAT (MAP fn_insts ctx.ctx_functions) = state_insts st
Proof
  rpt gen_tac >> simp[extract_context_with_internals_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule package_internal_blocks_partition >>
  simp[mk_venom_context_def, fn_insts_def, mk_raw_function_def,
       fn_insts_blocks_flat, state_insts_def, all_blocks_def] >>
  disch_then SUBST1_TAC >>
  simp[MAP_APPEND, FLAT_APPEND, MAP_FLAT, MAP_COMPOSE, combinTheory.o_DEF] >>
  qpat_x_assum `package_internal_blocks _ _ = _` kall_tac >>
  Induct_on `functions` >>
  simp[fn_insts_def, fn_insts_blocks_flat, FLAT_APPEND]
QED
