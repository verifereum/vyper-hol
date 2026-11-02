(* Separate the source-instruction permutation from terminal operand flips. *)
Theory dftFrameNormalize
Ancestors
  dftFrameOrder dftSsaPreserve dftStructural dftHelpers dftScheduleOrder
  dftCorrectness venomInst venomWf sorting list

Definition dft_flip_inst_def:
  dft_flip_inst i j <=>
    j = i \/ (is_flippable i.inst_opcode /\ j = flip_operands i)
End

Definition dft_flip_block_def:
  dft_flip_block b c <=> b.bb_label = c.bb_label /\
    LIST_REL dft_flip_inst b.bb_instructions c.bb_instructions
End

Definition dft_flip_fn_def:
  dft_flip_fn f g <=> f.fn_name = g.fn_name /\
    LIST_REL dft_flip_block f.fn_blocks g.fn_blocks
End

Theorem dft_flip_inst_id:
  dft_flip_inst i j ==> j.inst_id = i.inst_id
Proof
  simp[dft_flip_inst_def] >> metis_tac[flip_operands_inst_id]
QED

Theorem from_block_normalize:
  !body. EVERY (from_block src) body ==>
    ?n. EVERY (\i. MEM i src /\ ~is_pseudo i.inst_opcode) n /\
        MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) body /\
        LIST_REL dft_flip_inst n body
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  qpat_x_assum `from_block _ _` mp_tac >>
  simp[from_block_def] >> strip_tac >>
  qexists_tac `j::n` >> simp[dft_flip_inst_def] >>
  metis_tac[flip_operands_inst_id]
QED

Theorem source_ids_perm:
  EVERY (\i. MEM i src) n /\
  ALL_DISTINCT (MAP (\i. i.inst_id) src) /\
  PERM (MAP (\i. i.inst_id) n) (MAP (\i. i.inst_id) src) ==>
  PERM n src
Proof
  rpt strip_tac >>
  mp_tac (Q.ISPECL [`\i:instruction. i.inst_id`, `\i:instruction. i`,
                    `src:instruction list`, `n:instruction list`] PERM_TRANSFER) >>
  simp[MAP_ID] >> impl_tac
  >- (conj_tac >- metis_tac[PERM_SYM] >> simp[] >>
      gvs[EVERY_MEM] >> metis_tac[all_distinct_map_mem_inj]) >>
  metis_tac[PERM_SYM]
QED

Theorem dft_block_normalize_body:
  dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  ?body n.
    bb'.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ body /\
    EVERY (\i. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode) n /\
    MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) body /\
    LIST_REL dft_flip_inst n body /\
    PERM (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ n)
         bb.bb_instructions
Proof
  strip_tac >>
  drule (iffLR dft_block_rel_def) >> strip_tac >>
  drule from_block_normalize >> strip_tac >>
  rename1 `LIST_REL dft_flip_inst n target_body` >>
  qexistsl [`target_body`, `n`] >> simp[] >>
  irule source_ids_perm >> simp[EVERY_APPEND, EVERY_FILTER, EVERY_MEM] >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  irule PERM_TRANS >>
  qexists_tac `MAP (\i. i.inst_id) bb'.bb_instructions` >>
  conj_tac >- simp[MAP_APPEND] >>
  metis_tac[dft_block_rel_ids_perm]
QED

Theorem dft_flip_list_refl:
  !xs. LIST_REL dft_flip_inst xs xs
Proof
  Induct >> simp[dft_flip_inst_def]
QED

Theorem dft_block_normalize:
  dft_block_rel bb bb' /\ pseudos_prefix bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  ?n. PERM bb.bb_instructions n /\
      MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) bb'.bb_instructions /\
      LIST_REL dft_flip_inst n bb'.bb_instructions /\
      n = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
          FILTER (\i. ~is_pseudo i.inst_opcode) n
Proof
  rpt strip_tac >> drule_all dft_block_normalize_body >> strip_tac >>
  qexists_tac `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ n` >>
  conj_tac >- metis_tac[PERM_SYM] >>
  conj_tac >- simp[MAP_APPEND] >>
  conj_tac >- simp[LIST_REL_APPEND_suff, dft_flip_list_refl] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) n = n` by
    (simp[FILTER_EQ_ID] >> gvs[EVERY_MEM]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode)
     (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER] >>
  simp[FILTER_APPEND_DISTRIB]
QED

Theorem dft_normalize_must_order:
  dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  PERM bb.bb_instructions n /\
  MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) bb'.bb_instructions /\
  ~is_pseudo a.inst_opcode /\ ~is_pseudo b.inst_opcode /\
  id_before bb.bb_instructions a b /\ dft_must_order a b ==>
  id_before n a b
Proof
  rpt strip_tac >>
  `MEM a bb.bb_instructions /\ MEM b bb.bb_instructions` by
    metis_tac[id_before_mem] >>
  `MEM a n /\ MEM b n` by metis_tac[PERM_MEM_EQ] >>
  irule id_before_ids_invert >> simp[] >> conj_tac
  >- metis_tac[ALL_DISTINCT_PERM, PERM_MAP] >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) a.inst_id b.inst_id`
    by metis_tac[id_before_map] >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  simp[MAP_APPEND, id_before_append] >>
  disj2_tac >> disj1_tac >> first_x_assum irule >> simp[]
QED
