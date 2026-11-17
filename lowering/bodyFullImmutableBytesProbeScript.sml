(* The padding obligation of an immutable Bytes[40] memory copy. *)
Theory bodyFullImmutableBytesProbe
Ancestors
  bodyFullImmutableStoreProbe representationCleanPtr bodyPtrDefs immSectionDead
  ctorDeployDeadSection ctorDeployDeadSectionFrame
  valueEncoding valueEncodingDefs valueEncodingProps
  compileVyper vyperTypeSystem vyperTyping vyperValue vyperAST
  venomState list finite_map pred_set arithmetic words

Theorem immutable_bytes40_copied_taint_dead:
  (!mem. mem_agree_outside dirty mem0 mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic 40))) (BytesV bs) src mem) /\
  LENGTH bs < dimword (:256) /\
  mem_word_at off sec = n2w (LENGTH bs) /\
  32 + LENGTH bs <= copied /\
  off <= i /\ i < off + type_memory_size (BaseTV (BytesT (Dynamic 40))) /\
  i IN ((dirty DIFF {j | off <= j /\ j < off + copied}) UNION
         {off + k | k < copied /\ src + k IN dirty}) ==>
  mem_dead_bytes sec off (BaseTV (BytesT (Dynamic 40))) i
Proof
  strip_tac >>
  `(!j. src <= j /\ j < src + 32 ==> j NOTIN dirty) /\
   (!j. src + 32 <= j /\ j < src + 32 + LENGTH bs ==> j NOTIN dirty)` by
    (drule robust_val_in_memory_bytes_clean >> simp[]) >>
  `!k. k < 32 + LENGTH bs ==> src + k NOTIN dirty` by
    (rpt strip_tac >> Cases_on `k < 32`
     >- (qpat_x_assum `!j. src <= j /\ j < src + 32 ==> _`
           (qspec_then `src+k` mp_tac) >> simp[] >> decide_tac) >>
     qpat_x_assum `!j. src + 32 <= j /\ _ ==> _`
       (qspec_then `src+k` mp_tac) >> simp[] >> decide_tac) >>
  `off + 32 + LENGTH bs <= i` by
    (qpat_x_assum `i IN _` mp_tac >>
     simp[IN_UNION, IN_DIFF] >> strip_tac
     >- decide_tac >> gvs[] >>
     `~(k < 32 + LENGTH bs)` by metis_tac[ADD_COMM] >> decide_tac) >>
  simp[mem_dead_bytes_def, w2n_n2w, LESS_MOD]
QED

(* Changing one immutable cannot change the deadness in another declaration. *)
Theorem immutable_other_dead_frame:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  ~(off <= i /\ i < off + type_memory_size tv) /\
  imm_section_dead tops sec1 i ==>
  imm_section_dead tops sec2 i
Proof
  strip_tac >>
  qpat_x_assum `imm_section_dead _ _ _`
    (mp_tac o REWRITE_RULE [imm_section_dead_def]) >>
  disch_then (qx_choosel_then [`pre2`, `vis2`, `name2`, `ty2`, `slot2`, `post2`, `tv2`]
    strip_assume_tac) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
   type_memory_size tv /\
   type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty2 =
   type_memory_size tv2` by metis_tac[imm_frame_size] >>
  Q.SUBGOAL_THEN `pre = pre2 \/ off + type_memory_size tv <=
      compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2 \/
    compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2 +
      type_memory_size tv2 <= off` assume_tac
  >-
    (`pre ++ VariableDecl vis Immutable name ty slot :: post =
      pre2 ++ VariableDecl vis2 Immutable name2 ty2 slot2 :: post2` by metis_tac[] >>
     drule imm_frame_occurrence_separation >>
     disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
     simp[] >> metis_tac[]) >>
  Cases_on `pre = pre2`
  >- (gvs[] >>
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
      drule (CONJUNCT1 mem_dead_bytes_range) >>
      simp[GSYM APPEND_ASSOC] >> decide_tac) >>
  fs[] >>
  `mem_dead_bytes sec2
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2) tv2 =
   mem_dead_bytes sec1
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre2) tv2` by
    (irule mem_dead_bytes_frame >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> gvs[] >> decide_tac) >>
  simp[imm_section_dead_def] >>
  qexistsl_tac [`pre2`, `vis2`, `name2`, `ty2`, `slot2`, `post2`, `tv2`] >> gvs[]
QED

Theorem immutable_bytes40_section_taint:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name (BaseT (BytesT (Dynamic 40))) slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off +
        type_memory_size (BaseTV (BytesT (Dynamic 40)))) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < lo /\ j IN dirty ==> imm_section_dead tops sec1 j) /\
  (!mem. mem_agree_outside dirty mem0 mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic 40))) (BytesV bs) src mem) /\
  LENGTH bs < dimword (:256) /\
  mem_word_at off sec2 = n2w (LENGTH bs) /\
  32 + LENGTH bs <= copied /\
  copied <= type_memory_size (BaseTV (BytesT (Dynamic 40))) /\
  i < lo /\
  i IN ((dirty DIFF {j | off <= j /\ j < off + copied}) UNION
         {off + k | k < copied /\ src + k IN dirty}) ==>
  imm_section_dead tops sec2 i
Proof
  strip_tac >>
  Cases_on `off <= i /\ i < off + type_memory_size (BaseTV (BytesT (Dynamic 40)))`
  >- (`mem_dead_bytes sec2 off (BaseTV (BytesT (Dynamic 40))) i` by
        metis_tac[immutable_bytes40_copied_taint_dead] >>
      simp[imm_section_dead_def] >>
      qexistsl_tac [`pre`, `vis`, `name`, `BaseT (BytesT (Dynamic 40))`,
        `slot`, `post`, `BaseTV (BytesT (Dynamic 40))`] >>
      simp[evaluate_type_def, type_slot_size_def, vfmConstantsTheory.word_size_def,
           dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
      metis_tac[]) >>
  `i IN dirty` by
    (qpat_x_assum `i IN _` mp_tac >>
     qpat_x_assum `~(off <= i /\ i < off + _)` mp_tac >>
     qpat_x_assum `copied <= _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[IN_UNION, IN_DIFF] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `imm_section_dead tops sec1 i` by metis_tac[] >>
  mp_tac (Q.INST [`tops` |-> `tops`, `pre` |-> `pre`, `vis` |-> `vis`,
    `name` |-> `name`, `ty` |-> `BaseT (BytesT (Dynamic 40))`,
    `slot` |-> `slot`, `post` |-> `post`,
    `tv` |-> `BaseTV (BytesT (Dynamic 40))`, `off` |-> `off`,
    `sec1` |-> `sec1`, `sec2` |-> `sec2`, `i` |-> `i`]
    (SPEC_ALL immutable_other_dead_frame)) >>
  simp[evaluate_type_def, type_slot_size_def, vfmConstantsTheory.word_size_def,
       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  disch_then irule >>
  qpat_x_assum `~(off <= i /\ i < off + _)` mp_tac >> simp[]
QED

