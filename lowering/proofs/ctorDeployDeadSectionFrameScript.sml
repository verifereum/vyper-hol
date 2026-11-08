(* imm_section_dead is fixed by the immutables section's live bytes. *)
Theory ctorDeployDeadSectionFrame
Ancestors
  ctorDeployDeadSection ctorDeployDefs immSectionDead immutableSectionRel immutableValue
  immutableEncoding valueEncoding compileVyper structFieldsProps entryStateRel
  list rich_list

Theorem imm_frame_size:
  struct_args_unique tops /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
  type_memory_size tv
Proof
  strip_tac >>
  qspecl_then [`ARB with ce_struct_fields := make_struct_fields_map tops`, `ty`]
    mp_tac type_mem_bytes_type_memory_bytes >>
  simp[] >> disch_then SUBST1_TAC >>
  irule make_struct_fields_map_memory_size >> simp[] >> metis_tac[]
QED

Theorem imm_frame_len_cons[local]:
  compute_immutables_len sft (h::xs) =
  compute_immutables_len sft [h] + compute_immutables_len sft xs
Proof
  rewrite_tac[GSYM compute_immutables_len_append] >> simp[]
QED

Theorem imm_frame_occurrence_cons[local]:
  (!q v n ty sl r v' n' ty' sl' r'.
    p ++ VariableDecl v Immutable n ty sl :: r =
    q ++ VariableDecl v' Immutable n' ty' sl' :: r' ==>
    p = q \/
    compute_immutables_len sft p + type_mem_bytes sft ty <=
      compute_immutables_len sft q \/
    compute_immutables_len sft q + type_mem_bytes sft ty' <=
      compute_immutables_len sft p) ==>
  h::p ++ VariableDecl v Immutable n ty sl :: r =
  k::q ++ VariableDecl v' Immutable n' ty' sl' :: r' ==>
  h::p = k::q \/
  compute_immutables_len sft (h::p) + type_mem_bytes sft ty <=
    compute_immutables_len sft (k::q) \/
  compute_immutables_len sft (k::q) + type_mem_bytes sft ty' <=
    compute_immutables_len sft (h::p)
Proof
  simp[] >> rpt strip_tac >>
  first_x_assum (drule o SIMP_RULE (srw_ss()) []) >>
  pure_once_rewrite_tac[imm_frame_len_cons] >>
  strip_tac >- simp[] >> disj2_tac >> decide_tac
QED

Theorem imm_frame_occurrence_separation:
  !p q v n ty sl r v' n' ty' sl' r'.
    p ++ VariableDecl v Immutable n ty sl :: r =
    q ++ VariableDecl v' Immutable n' ty' sl' :: r' ==>
    p = q \/
    compute_immutables_len sft p + type_mem_bytes sft ty <=
      compute_immutables_len sft q \/
    compute_immutables_len sft q + type_mem_bytes sft ty' <=
      compute_immutables_len sft p
Proof
  Induct_on `p`
  >- (Cases_on `q` >> simp[compute_immutables_len_def] >>
      rpt strip_tac >> gvs[compute_immutables_len_def]) >>
  Cases_on `q`
  >- (simp[] >> rpt strip_tac >> gvs[compute_immutables_len_def]) >>
  metis_tac[imm_frame_occurrence_cons]
QED

Theorem imm_frame_restrict:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  off <= j /\ j < off + type_memory_size tv ==>
  (imm_section_dead tops sec j <=> mem_dead_bytes sec off tv j)
Proof
  rpt strip_tac >> eq_tac
  >- (rewrite_tac[imm_section_dead_def] >> strip_tac >>
      drule (CONJUNCT1 mem_dead_bytes_range) >> strip_tac >>
      `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
       type_memory_size tv` by metis_tac[imm_frame_size] >>
      rename1 `evaluate_type (type_env tops) ty' = SOME tv'` >>
      `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
       type_memory_size tv'` by metis_tac[imm_frame_size] >>
      `pre ++ VariableDecl vis Immutable name ty slot :: post =
       pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'`
        by metis_tac[] >>
      drule imm_frame_occurrence_separation >>
      disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
      strip_tac
      >- (fs[] >> gvs[])
      >- (ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
          qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >> gvs[] >> decide_tac) >>
      ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
      qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >> gvs[] >> decide_tac) >>
  rewrite_tac[imm_section_dead_def] >> strip_tac >>
  qexistsl_tac [`pre`, `vis`, `name`, `ty`, `slot`, `post`, `tv`] >> gvs[]
QED

Theorem imm_frame_value:
  struct_args_unique tops /\ LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
       EL j sec2 = EL j sec1) /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  mem_dead_bytes sec2
    (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) tv =
  mem_dead_bytes sec1
    (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) tv
Proof
  rpt strip_tac >> irule mem_dead_bytes_frame >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  metis_tac[imm_frame_restrict]
QED

Theorem imm_section_dead_frame:
  !tops sec1 sec2.
    struct_args_unique tops /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
         EL j sec2 = EL j sec1) ==>
    imm_section_dead tops sec2 = imm_section_dead tops sec1
Proof
  rpt strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  rewrite_tac[imm_section_dead_def] >>
  `!pre vis name ty slot post tv.
     tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
     evaluate_type (type_env tops) ty = SOME tv ==>
     mem_dead_bytes sec2
       (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) tv =
     mem_dead_bytes sec1
       (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) tv`
    by (rpt strip_tac >> irule imm_frame_value >> metis_tac[]) >>
  metis_tac[]
QED
