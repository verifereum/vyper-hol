(* Hashing helpers first emit a load or a private allocation. *)
Theory builtinHashFirstEmission
Ancestors
  compilerFirstEmission builtinHashing fragExec compileEnv emitHelper venomInst context

fun hash_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
       [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- hash_append_tac >> rpt gen_tac >> hash_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> hash_append_tac,
    IF_CASES_TAC >> hash_append_tac]) g;
fun hash_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> hash_append_tac) >>
   fs[cs_appends_def]) g;
fun hash_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun hash_strong_tac g =
  (FIRST [hash_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- hash_strong_tac >> hash_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- hash_strong_tac >> hash_tail_tac]) g;

Theorem first_emission_keccak256_word:
  !a x b. compile_keccak256_word v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_keccak256_word_def, compile_alloc_buffer_def] >>
  hash_strong_tac
QED

Theorem first_emission_keccak256_bytes:
  !a x b. compile_keccak256_bytes v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_keccak256_bytes_def] >> hash_strong_tac
QED

Theorem first_emission_keccak256_bytesm:
  !a x b. compile_keccak256_bytesm v n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_keccak256_bytesm_def, compile_alloc_buffer_def] >>
  hash_strong_tac
QED

Theorem first_emission_sha256_word:
  !a x b. compile_sha256_word v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_sha256_word_def, compile_alloc_buffer_def] >>
  hash_strong_tac
QED

Theorem first_emission_sha256_bytes:
  !a x b. compile_sha256_bytes v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_sha256_bytes_def, compile_alloc_buffer_def] >>
  hash_strong_tac
QED

Theorem first_emission_sha256_bytesm:
  !a x b. compile_sha256_bytesm v n a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_sha256_bytesm_def, compile_alloc_buffer_def] >>
  hash_strong_tac
QED

Theorem first_emission_method_id_hash:
  !a x b. compile_method_id_hash ty v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `ty` >> simp_tac (srw_ss()) [compile_method_id_hash_def]
  >~ [`compile_method_id_hash (BaseT bt)`] >- (
    Cases_on `bt` >> simp_tac (srw_ss()) [compile_method_id_hash_def]
    >~ [`compile_method_id_hash (BaseT (BytesT bound))`] >- (
      Cases_on `bound` >> simp_tac (srw_ss()) [compile_method_id_hash_def] >>
      FIRST [MATCH_ACCEPT_TAC first_emission_keccak256_bytesm,
             MATCH_ACCEPT_TAC first_emission_keccak256_bytes]) >>
    MATCH_ACCEPT_TAC first_emission_keccak256_bytes) >>
  MATCH_ACCEPT_TAC first_emission_keccak256_bytes
QED

Theorem first_emission_method_id_runtime:
  !a x b. compile_method_id_runtime ty v bytes4 a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_method_id_runtime_def, compile_alloc_buffer_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_method_id_hash >> hash_tail_tac
QED
