(* Scalar builtin prefixes emit before their straight-line suffixes. *)
Theory builtinScalarFirstEmission
Ancestors
  compilerFirstEmission contextFirstEmission builtinMisc builtinMath
  builtinSimple exprLowering fragExec compileEnv emitHelper venomInst context

fun scalar_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
       [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- scalar_append_tac >> rpt gen_tac >> scalar_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> scalar_append_tac,
    IF_CASES_TAC >> scalar_append_tac]) g;
fun scalar_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> scalar_append_tac) >>
   fs[cs_appends_def]) g;
fun scalar_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun scalar_strong_tac g =
  (FIRST [scalar_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- scalar_strong_tac >> scalar_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- scalar_strong_tac >> scalar_tail_tac]) g;

Theorem first_emission_blockhash:
  !a x b. compile_blockhash v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_blockhash_def] >> scalar_strong_tac
QED

Theorem first_emission_blobhash:
  !a x b. compile_blobhash v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_blobhash_def] >> scalar_emit_tac
QED

Theorem first_emission_floor:
  !a x b. compile_floor v d a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_floor_def, compile_select_def] >> scalar_strong_tac
QED

Theorem first_emission_ceil:
  !a x b. compile_ceil v d a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_ceil_def, compile_select_def] >> scalar_strong_tac
QED

Theorem first_emission_pow_mod256:
  !a x b. compile_pow_mod256 v w a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_pow_mod256_def] >> scalar_emit_tac
QED

Theorem first_emission_addmod:
  !a x b. compile_addmod v w z a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_addmod_def] >> scalar_strong_tac
QED

Theorem first_emission_mulmod:
  !a x b. compile_mulmod v w z a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_mulmod_def] >> scalar_strong_tac
QED

Theorem first_emission_shift:
  !a x b. compile_shift v w signed a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_shift_def, compile_select_def] >> scalar_strong_tac
QED

Theorem first_emission_builtin_calldatasize:
  !a x b. compile_builtin_calldatasize a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_builtin_calldatasize_def] >> scalar_emit_tac
QED

Theorem first_emission_builtin_len:
  !a x b. compile_builtin_len ctor imm p loc a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_builtin_len_def] >>
  MATCH_ACCEPT_TAC first_emission_ptr_load
QED

Theorem first_emission_ecrecover:
  !a x b. compile_ecrecover h v r s a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_ecrecover_def, compile_alloc_buffer_def] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- scalar_strong_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail st0 = (y,c)` >>
  `cs_appends tail` by
    (simp_tac bool_ss [Abbr `tail`] >> scalar_append_tac) >>
  fs[cs_appends_def]
QED

Theorem first_emission_ecadd_points:
  !a x b. compile_ecadd_points p q a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_ecadd_points_def, compile_alloc_buffer_def] >>
  scalar_strong_tac
QED

Theorem first_emission_ecmul_point:
  !a x b. compile_ecmul_point p v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_ecmul_point_def, compile_alloc_buffer_def] >>
  scalar_strong_tac
QED

Theorem first_emission_env_var:
  !a x b. compile_env_var item a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `item` >> simp_tac bool_ss [compile_env_var_def] >> scalar_strong_tac
QED

Theorem first_emission_as_wei_value_decimal:
  !a x b. compile_as_wei_value_decimal v scale d a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_as_wei_value_decimal_def] >> scalar_strong_tac
QED

Theorem first_emission_as_wei_value_int:
  !a x b. compile_as_wei_value_int v scale signed a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `scale = 1` >> asm_simp_tac bool_ss [compile_as_wei_value_int_def]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_strong >> scalar_strong_tac
QED
