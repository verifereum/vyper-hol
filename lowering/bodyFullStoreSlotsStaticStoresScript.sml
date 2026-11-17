(* Store-emission provenance, independent of execution and ghost state. *)
Theory bodyFullStoreSlotsStaticStores
Ancestors
  bodyFullStoreSlotsStaticCode exprSimAbiDecodeSiteCoverage
  exprSimAbiEncodeObliviousCode exprSimAbiGasBridge context compileEnv
  fragExec exprLoweringProps emitHelper list

Theorem slots_relation_bind[local]:
  (!a b c. R a b /\ R b c ==> R a c) /\
  (!a. R a (SND (m a))) /\ (!x a. R a (SND (f x a))) ==>
  !a. R a (SND (comp_bind m f a))
Proof
  rw[comp_bind_def] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> qexists_tac `cs'` >> simp[] >>
  qpat_x_assum `!a. R a (SND (m a))` (qspec_then `a` mp_tac) >> simp[]
QED

Theorem slots_relation_ignore_bind[local]:
  (!a b c. R a b /\ R b c ==> R a c) /\
  (!a. R a (SND (m a))) /\ (!a. R a (SND (n a))) ==>
  !a. R a (SND (comp_ignore_bind m n a))
Proof
  strip_tac >> simp[comp_ignore_bind_def] >>
  irule slots_relation_bind >> asm_rewrite_tac[]
QED

Theorem slots_relation_primitives[local]:
  (!tr a b c. R tr a b /\ R tr b c ==> R tr a c) /\
  (!tr a. R tr a a) /\
  (!tr opc ops outs a. opc <> SSTORE /\ opc <> TSTORE ==>
    R tr a (SND (emit_inst opc ops outs a))) /\
  (!tr opc ops a. opc <> SSTORE /\ opc <> TSTORE ==>
    R tr a (SND (emit_op opc ops a))) /\
  (!tr opc ops a. opc <> SSTORE /\ opc <> TSTORE ==>
    R tr a (SND (emit_void opc ops a))) /\
  (!tr dst v a. R tr a (SND (emit_void (if tr then TSTORE else SSTORE) [dst;v] a))) /\
  (!tr a. R tr a (SND (fresh_var a))) /\
  (!tr lab a. R tr a (SND (fresh_label lab a))) /\
  (!tr lab a. R tr a (SND (new_block lab a))) ==>
  (!tr src dst cnt a. R tr a (SND
    (compile_word_copy_loop_op src dst cnt LocMemory
       (if tr then LocTransient else LocStorage) F a))) /\
  (!tr src a. R tr a (SND (compile_bytestring_word_count src a))) /\
  (!tr src off a. R tr a (SND (compile_lit_byte_offset src off a)))
Proof
  strip_tac >> rpt conj_tac
  >- (rpt gen_tac >>
      `!a b c. R tr a b /\ R tr b c ==> R tr a c` by metis_tac[] >>
      qpat_assum `!tr dst v a. R tr a (SND (emit_void _ [dst;v] a))`
        (qspec_then `tr` assume_tac) >>
      simp[compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
           word_scale_def] >>
      Cases_on `tr` >> gvs[word_scale_def, compile_ptr_load_def,
                             compile_ptr_store_def] >>
      ntac 5 (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
        asm_rewrite_tac[] >> simp[comp_return_def] >> rpt conj_tac >> rpt gen_tac) >>
      ntac 5 (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
        asm_rewrite_tac[] >> simp[comp_return_def] >> rpt conj_tac >> rpt gen_tac) >>
      rpt (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
        asm_rewrite_tac[] >> simp[comp_return_def] >> rpt conj_tac >> rpt gen_tac) >>
      metis_tac[COND_CLAUSES])
  >- (rpt gen_tac >>
      `!a b c. R tr a b /\ R tr b c ==> R tr a c` by metis_tac[] >>
      simp[compile_bytestring_word_count_def] >>
      rpt (irule slots_relation_bind >> simp[] >> asm_rewrite_tac[] >>
           rpt conj_tac >> rpt gen_tac) >> simp[]) >>
  rpt gen_tac >> simp[compile_lit_byte_offset_def] >> IF_CASES_TAC >>
  simp[comp_return_def] >> Cases_on `src` >> simp[comp_return_def]
QED

Theorem slots_relation_family[local]:
  (!tr a b c. R tr a b /\ R tr b c ==> R tr a c) /\
  (!tr a. R tr a a) /\
  (!tr opc ops outs a. opc <> SSTORE /\ opc <> TSTORE ==>
    R tr a (SND (emit_inst opc ops outs a))) /\
  (!tr opc ops a. opc <> SSTORE /\ opc <> TSTORE ==>
    R tr a (SND (emit_op opc ops a))) /\
  (!tr opc ops a. opc <> SSTORE /\ opc <> TSTORE ==>
    R tr a (SND (emit_void opc ops a))) /\
  (!tr dst v a. R tr a (SND (emit_void (if tr then TSTORE else SSTORE) [dst;v] a))) /\
  (!tr a. R tr a (SND (fresh_var a))) /\
  (!tr lab a. R tr a (SND (fresh_label lab a))) /\
  (!tr lab a. R tr a (SND (new_block lab a))) ==>
  (!cenv src dst ty tr a. R tr a (SND (compile_store_slots cenv src dst ty tr a))) /\
  (!cenv src dst ms mo so tr a.
    R tr a (SND (compile_store_slots_members cenv src dst ms mo so tr a))) /\
  (!cenv src dst elem cnt tr a.
    R tr a (SND (compile_copy_elements_to_slots cenv src dst elem cnt tr a)))
Proof
  strip_tac >>
  `(!tr src dst cnt a. R tr a (SND
    (compile_word_copy_loop_op src dst cnt LocMemory
       (if tr then LocTransient else LocStorage) F a))) /\
   (!tr src a. R tr a (SND (compile_bytestring_word_count src a))) /\
   (!tr src off a. R tr a (SND (compile_lit_byte_offset src off a)))` by
    (irule slots_relation_primitives >> asm_rewrite_tac[]) >>
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- (pure_rewrite_tac[cj 2 compile_store_slots_def, comp_return_def] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `!a b c. R tr a b /\ R tr b c ==> R tr a c` by metis_tac[] >>
      pure_rewrite_tac[cj 3 compile_store_slots_def] >>
      rpt (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
           simp[] >> asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac)) >>
  rpt gen_tac >> strip_tac >>
  `!a b c. R tr a b /\ R tr b c ==> R tr a c` by metis_tac[] >>
  pure_rewrite_tac[cj 4 compile_store_slots_def] >> simp[] >>
  ntac 5 (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
       simp[comp_return_def] >> asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac) >>
  ntac 5 (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
       simp[comp_return_def] >> asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac) >>
  rpt (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
       simp[comp_return_def] >> asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac) >> simp[]
QED

Resume slots_relation_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  `!a b c. R tr a b /\ R tr b c ==> R tr a c` by metis_tac[] >>
  pure_once_rewrite_tac[cj 1 compile_store_slots_def] >> simp[] >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields ty`
  >- (simp[] >> IF_CASES_TAC
      >- (irule slots_relation_bind >> simp[] >> asm_rewrite_tac[]) >>
      Cases_on `tr` >>
      simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
           compile_word_copy_loop_def] >>
      irule slots_relation_ignore_bind >> simp[comp_return_def] >>
      asm_rewrite_tac[] >> metis_tac[COND_CLAUSES]) >>
  simp[] >> Cases_on `is_bytestring_type ty`
  >- (simp[] >> irule slots_relation_bind >> simp[] >> asm_rewrite_tac[] >> gen_tac >> simp[] >>
      irule slots_relation_ignore_bind >> simp[comp_return_def] >>
      asm_rewrite_tac[] >> metis_tac[COND_CLAUSES]) >>
  simp[] >> IF_CASES_TAC >- simp[] >>
  Cases_on `ty` >> gvs[] >>
  rename1 `ArrayT elem bd` >> Cases_on `bd` >> gvs[] >>
  rpt (FIRST [irule slots_relation_bind, irule slots_relation_ignore_bind] >>
       simp[] >> asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac)
QED

Finalise slots_relation_family

Theorem slots_sites_compose[local]:
  cs_extends a b /\ cs_extends b c /\
  (!i. MEM i (frag_code a b) /\
       (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
       ?u w. Q i u w /\ cs_extends a u /\ cs_extends u w /\ cs_extends w b) /\
  (!i. MEM i (frag_code b c) /\
       (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
       ?u w. Q i u w /\ cs_extends b u /\ cs_extends u w /\ cs_extends w c) ==>
  !i. MEM i (frag_code a c) /\
       (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
       ?u w. Q i u w /\ cs_extends a u /\ cs_extends u w /\ cs_extends w c
Proof
  rpt strip_tac >>
  drule_all exprSimAbiDecodeSuffixWritesTheory.abi_decode_frag_code_split >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem slots_sites_readonly[local]:
  code_action (\opc. opc <> SSTORE /\ opc <> TSTORE) m ==>
  !a. cs_extends a (SND (m a)) /\
    !i. MEM i (frag_code a (SND (m a))) /\
      (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
      ?u w. Q i u w /\ cs_extends a u /\ cs_extends u w /\ cs_extends w (SND (m a))
Proof
  rw[code_action_def] >>
  first_x_assum (qspecl_then [`a`,`FST (m a)`,`SND (m a)`] mp_tac) >>
  simp[] >> strip_tac
  >- metis_tac[code_step_extends] >>
  gvs[code_step_def, EVERY_MEM] >> metis_tac[]
QED

Theorem slots_sites_emit[local]:
  !tr dst v a.
    cs_extends a (SND (emit_void (if tr then TSTORE else SSTORE) [dst;v] a)) /\
    !i. MEM i (frag_code a (SND (emit_void (if tr then TSTORE else SSTORE) [dst;v] a))) /\
      (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
      ?u w. (i.inst_opcode = (if tr then TSTORE else SSTORE) /\
        ?p q. i.inst_operands = [p;q] /\ i.inst_outputs = [] /\
          emit_void (if tr then TSTORE else SSTORE) [p;q] u = ((),w) /\
          i = mk_inst u.cs_next_id (if tr then TSTORE else SSTORE) [p;q] []) /\
        cs_extends a u /\ cs_extends u w /\
        cs_extends w (SND (emit_void (if tr then TSTORE else SSTORE) [dst;v] a))
Proof
  rpt gen_tac >> conj_asm1_tac
  >- (irule code_step_extends >>
      qexists_tac `(\opc. T)` >>
      mp_tac code_action_emit_void >> simp[code_action_def]) >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
       frag_code_def, emitted_blocks_def, emitted_insts_def, DROP_APPEND] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`a`, `SND (emit_void (if tr then TSTORE else SSTORE) [dst;v] a)`] >>
  simp[mk_inst_def, cs_extends_refl] >>
  qexistsl_tac [`dst`,`v`] >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def]
QED

Theorem store_slots_store_site_family[local]:
  (!cenv src dst ty tr a.
    cs_extends a (SND (compile_store_slots cenv src dst ty tr a)) /\
    !i. MEM i (frag_code a (SND (compile_store_slots cenv src dst ty tr a))) /\
      (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
      ?u w. (i.inst_opcode = (if tr then TSTORE else SSTORE) /\
        ?p q. i.inst_operands = [p;q] /\ i.inst_outputs = [] /\
          emit_void (if tr then TSTORE else SSTORE) [p;q] u = ((),w) /\
          i = mk_inst u.cs_next_id (if tr then TSTORE else SSTORE) [p;q] []) /\
        cs_extends a u /\ cs_extends u w /\
        cs_extends w (SND (compile_store_slots cenv src dst ty tr a))) /\
  (!cenv src dst ms mo so tr a.
    cs_extends a (SND (compile_store_slots_members cenv src dst ms mo so tr a)) /\
    !i. MEM i (frag_code a (SND (compile_store_slots_members cenv src dst ms mo so tr a))) /\
      (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
      ?u w. (i.inst_opcode = (if tr then TSTORE else SSTORE) /\
        ?p q. i.inst_operands = [p;q] /\ i.inst_outputs = [] /\
          emit_void (if tr then TSTORE else SSTORE) [p;q] u = ((),w) /\
          i = mk_inst u.cs_next_id (if tr then TSTORE else SSTORE) [p;q] []) /\
        cs_extends a u /\ cs_extends u w /\
        cs_extends w (SND (compile_store_slots_members cenv src dst ms mo so tr a))) /\
  (!cenv src dst elem cnt tr a.
    cs_extends a (SND (compile_copy_elements_to_slots cenv src dst elem cnt tr a)) /\
    !i. MEM i (frag_code a (SND (compile_copy_elements_to_slots cenv src dst elem cnt tr a))) /\
      (i.inst_opcode = SSTORE \/ i.inst_opcode = TSTORE) ==>
      ?u w. (i.inst_opcode = (if tr then TSTORE else SSTORE) /\
        ?p q. i.inst_operands = [p;q] /\ i.inst_outputs = [] /\
          emit_void (if tr then TSTORE else SSTORE) [p;q] u = ((),w) /\
          i = mk_inst u.cs_next_id (if tr then TSTORE else SSTORE) [p;q] []) /\
        cs_extends a u /\ cs_extends u w /\
        cs_extends w (SND (compile_copy_elements_to_slots cenv src dst elem cnt tr a)))
Proof
  irule slots_relation_family >> rpt conj_tac
  >- (rpt strip_tac
      >- metis_tac[cs_extends_trans] >>
      irule slots_sites_compose >> metis_tac[])
  >- simp[cs_extends_refl, frag_code_def, emitted_blocks_def, emitted_insts_def]
  >- (rpt strip_tac >> irule slots_sites_readonly >> simp[code_action_emit_inst])
  >- (rpt strip_tac >> irule slots_sites_readonly >> simp[code_action_emit_op])
  >- (rpt strip_tac >> irule slots_sites_readonly >> simp[code_action_emit_void])
  >- ACCEPT_TAC slots_sites_emit
  >- (rpt gen_tac >> irule slots_sites_readonly >> simp[code_action_fresh_var])
  >- (rpt gen_tac >> irule slots_sites_readonly >> simp[code_action_fresh_label]) >>
  rpt gen_tac >> irule slots_sites_readonly >> simp[code_action_new_block]
QED
