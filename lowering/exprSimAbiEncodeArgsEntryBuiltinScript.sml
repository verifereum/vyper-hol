Theory exprSimAbiEncodeArgsEntryBuiltin
Ancestors
  exprSimAbiEncodeArgsEntryCall exprSimAbiEncodeArgsEntryPlace
  builtinSimple builtinMisc builtinSystem externalEntryShape
  compileEnv exprSimAbiEncodeArgsEntryValue exprSimAbiEncodeArgsEntryPrim
  exprSimAbiEncodeArgsEntry emitHelper exprLowering builtinMath builtinHashing

(* Let-bound compiler results use the same entry contract as monadic binds. *)
Theorem abi_args_entry_safe_pair:
  (!a x b. m a = (x,b) ==> cs_extends a b /\ abi_args_entry_safe a b) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c /\ abi_args_entry_safe b c) ==>
  !a y c. (\(x,b). k x b) (m a) = (y,c) ==>
    cs_extends a c /\ abi_args_entry_safe a c
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[abi_args_entry_safe_trans, cs_extends_trans]
QED

Theorem abi_args_entry_emitted_pair:
  (!a x b. m a = (x,b) ==> cs_extends a b /\ abi_args_entry_safe a b) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c /\
    (b.cs_current_insts = [] ==> abi_args_entry_emitted b c)) ==>
  !a y c. (\(x,b). k x b) (m a) = (y,c) ==>
    cs_extends a c /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a c)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[abi_args_entry_safe_def] >>
  metis_tac[abi_args_entry_emitted_mono, abi_args_entry_emitted_code_eq,
            cs_extends_trans]
QED

Theorem abi_args_entry_builtin_abs:
  !v a x b. compile_builtin_abs v a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  gen_tac >> rewrite_tac[compile_builtin_abs_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >>
  rpt (irule abi_args_entry_extends_bind >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, emit_void_labels, compile_select_labels] >>
  irule abi_args_entry_extends_ignore_bind >>
  simp[emit_void_labels, compile_select_labels]
QED

Theorem abi_args_entry_builtin_abs_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty Abs es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[exprLoweringTheory.compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  rpt gen_tac >> Cases_on `compile_builtin_abs v st1` >>
  simp[exprLoweringTheory.as_stack_val_def] >> strip_tac >> gvs[] >>
  metis_tac[abi_args_entry_builtin_abs]
QED

Theorem abi_args_entry_stack_val:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) ==>
  !a vv b. as_stack_val ty (m a) = (vv,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[exprLoweringTheory.as_stack_val_def] >> metis_tac[]
QED

Theorem abi_args_entry_ptr_val:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) ==>
  !a vv b. as_ptr_val ty loc (m a) = (vv,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[exprLoweringTheory.as_ptr_val_def] >> metis_tac[]
QED

Theorem abi_args_entry_blockhash:
  !v a x b. compile_blockhash v a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  gen_tac >> rewrite_tac[compile_blockhash_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind,
              irule abi_args_entry_extends_ignore_bind] >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, emit_void_labels]
QED

Theorem abi_args_entry_blobhash:
  !v a x b. compile_blobhash v a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_blobhash_def] >> rpt gen_tac >> strip_tac >>
  irule abi_args_entry_emit_op >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_builtin_blockhash_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty bi es a vv b.
    (bi = BlockHash \/ bi = BlobHash) /\
    compile_builtin_dispatch_body cfn ce rt ty bi es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >> (
    pop_assum mp_tac >> map_every qid_spec_tac [`b`, `vv`, `a`] >>
    simp[compile_builtin_dispatch_body_def, LET_THM] >>
    ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
    >- metis_tac[abi_args_entry_lower_value] >>
    gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
    metis_tac[abi_args_entry_blockhash, abi_args_entry_blobhash])
QED

Theorem abi_args_entry_neg:
  !v ty a x b. compile_neg v ty a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 2 gen_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> irule abi_args_entry_extends_ignore_bind >>
  simp[emit_void_labels, emit_op_labels]
QED

Theorem abi_args_entry_builtin_neg_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty Neg es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
  metis_tac[abi_args_entry_neg]
QED

Theorem abi_args_entry_floor:
  !v d a x b. compile_floor v d a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_floor_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >>
  rpt (irule abi_args_entry_extends_bind >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, compile_select_labels]
QED

Theorem abi_args_entry_ceil:
  !v d a x b. compile_ceil v d a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 2 gen_tac >> rewrite_tac[compile_ceil_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >>
  rpt (irule abi_args_entry_extends_bind >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, compile_select_labels]
QED

Theorem abi_args_entry_builtin_round_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty bi es a vv b.
    (bi = Ceil \/ bi = Floor) /\
    compile_builtin_dispatch_body cfn ce rt ty bi es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >> (
    pop_assum mp_tac >> map_every qid_spec_tac [`b`, `vv`, `a`] >>
    simp[compile_builtin_dispatch_body_def, LET_THM] >>
    ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
    >- metis_tac[abi_args_entry_lower_value] >>
    gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
    metis_tac[abi_args_entry_ceil, abi_args_entry_floor])
QED

Theorem abi_args_entry_addmod:
  !u v w a x b. compile_addmod u v w a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_addmod_def, comp_ignore_bind_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `x` >>
      irule abi_args_entry_emit_void >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[emit_op_labels]
QED

Theorem abi_args_entry_mulmod:
  !u v w a x b. compile_mulmod u v w a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_mulmod_def, comp_ignore_bind_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `x` >>
      irule abi_args_entry_emit_void >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[emit_op_labels]
QED

Theorem abi_args_entry_powmod:
  !u v a x b. compile_pow_mod256 u v a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_pow_mod256_def] >> rpt gen_tac >> strip_tac >>
  irule abi_args_entry_emit_op >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_builtin_mod_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty bi es a vv b.
    (bi = AddMod \/ bi = MulMod \/ bi = PowMod256) /\
    compile_builtin_dispatch_body cfn ce rt ty bi es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >> (
    pop_assum mp_tac >> map_every qid_spec_tac [`b`, `vv`, `a`] >>
    simp[compile_builtin_dispatch_body_def, LET_THM] >>
    rpt (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
         >- metis_tac[abi_args_entry_lower_value] >> gen_tac) >>
    ho_match_mp_tac abi_args_entry_stack_val >>
    metis_tac[abi_args_entry_addmod, abi_args_entry_mulmod, abi_args_entry_powmod])
QED

Theorem abi_args_entry_invert:
  !v ty ce a x b. compile_invert v ty ce a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 3 gen_tac >> Cases_on `ty` >> simp[compile_invert_def, LET_THM] >>
  rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_builtin_not_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty Not es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> Cases_on `expr_type (HD es) = BaseT BoolT` >> simp[] >>
  ho_match_mp_tac abi_args_entry_stack_val
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[abi_args_entry_invert]
QED

Theorem abi_args_entry_safe_stack_val:
  (!a x b. m a = (x,b) ==> cs_extends a b /\ abi_args_entry_safe a b) ==>
  !a vv b. as_stack_val ty (m a) = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[as_stack_val_def] >> metis_tac[]
QED

Theorem abi_args_entry_builtin_len_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty Len es a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_safe_pair >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_safe_stack_val >>
  simp[compile_builtin_len_def] >>
  metis_tac[abi_args_entry_ptr_load, abi_args_entry_safe_def]
QED

Theorem abi_args_entry_builtin_len_emitted:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty Len es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
  simp[compile_builtin_len_def] >> metis_tac[abi_args_entry_ptr_load]
QED

Theorem abi_args_entry_hash_backend:
  !m v n.
    (m = compile_keccak256_word v \/ m = compile_keccak256_bytes v \/
     m = compile_keccak256_bytesm v n \/ m = compile_sha256_word v \/
     m = compile_sha256_bytes v \/ m = compile_sha256_bytesm v n) ==>
    !a x b. m a = (x,b) ==> cs_extends a b /\
      (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> (
    rewrite_tac[compile_keccak256_word_def, compile_keccak256_bytes_def,
      compile_keccak256_bytesm_def, compile_sha256_word_def,
      compile_sha256_bytes_def, compile_sha256_bytesm_def] >>
    ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
    >- FIRST [metis_tac[abi_args_entry_alloc_buffer],
              rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
              simp[] >> goal_assum (drule_at Any) >> simp[]] >>
    rpt gen_tac >>
    rpt (FIRST [irule abi_args_entry_extends_bind,
                irule abi_args_entry_extends_ignore_bind] >> conj_tac >>
         rpt gen_tac >> BETA_TAC) >>
    simp[emit_op_labels, emit_void_labels, compile_alloc_buffer_labels,
         comp_return_def, cs_extends_refl])
QED

Theorem abi_args_entry_builtin_hash_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty bi es a vv b.
    (bi = Keccak256 \/ bi = Sha256) /\
    compile_builtin_dispatch_body cfn ce rt ty bi es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >> (
    pop_assum mp_tac >> map_every qid_spec_tac [`b`, `vv`, `a`] >>
    simp[compile_builtin_dispatch_body_def, LET_THM] >>
    Cases_on `is_bytestring_type (expr_type (HD es))` >> simp[]
    >- (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
        >- metis_tac[abi_args_entry_lower_value] >>
        gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
        metis_tac[abi_args_entry_hash_backend]) >>
    Cases_on `expr_type (HD es)` >> simp[]
    >- (Cases_on `b` >> simp[]
        >- (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])
        >- (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])
        >- (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])
        >- (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])
        >- (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])
        >- (rename1 `BytesT bd` >> Cases_on `bd` >> simp[] >> (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])) >>
        (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend])) >>
    (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >>
          gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
          metis_tac[abi_args_entry_hash_backend]))
QED


Theorem abi_args_entry_pow_mod256:
  !v w a x b. compile_pow_mod256 v w a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[compile_pow_mod256_def] >> rpt gen_tac >> strip_tac >>
  irule abi_args_entry_emit_op >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_builtin_pow_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty PowMod256 es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_stack_val >>
  metis_tac[abi_args_entry_pow_mod256]
QED

Theorem abi_args_entry_builtin_calldatasize_dispatch:
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty CalldataLen es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  ho_match_mp_tac abi_args_entry_stack_val >>
  simp[compile_builtin_calldatasize_def] >> rpt gen_tac >> strip_tac >>
  irule abi_args_entry_emit_op >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_args_entry_env:
  !item a x b. compile_env_var item a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  Cases >> rewrite_tac[compile_env_var_def] >>
  FIRST [
    rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[],
    ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
    >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
    rpt gen_tac >> irule abi_args_entry_extends_bind >>
    simp[emit_op_labels]]
QED

Theorem abi_args_entry_builtin_env_dispatch:
  !ce rt ty es item a vv b.
    compile_builtin_dispatch_body cfn ce rt ty (Env item) es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 5 gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  ho_match_mp_tac abi_args_entry_stack_val >> metis_tac[abi_args_entry_env]
QED

Theorem abi_args_entry_ecrecover:
  !h v r s a x b. compile_ecrecover h v r s a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 4 gen_tac >> rewrite_tac[compile_ecrecover_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- metis_tac[abi_args_entry_alloc_buffer] >>
  rpt gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind,
              irule abi_args_entry_extends_ignore_bind] >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, emit_void_labels, compile_alloc_buffer_labels,
       comp_return_def, cs_extends_refl]
QED

Theorem abi_args_entry_builtin_ecrecover_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty ECRecover es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ntac 4 (ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
          >- metis_tac[abi_args_entry_lower_value] >> gen_tac) >>
  ho_match_mp_tac abi_args_entry_stack_val >>
  metis_tac[abi_args_entry_ecrecover]
QED

Theorem abi_args_entry_ec_points:
  !m p q.
    (m = compile_ecadd_points p q \/ m = compile_ecmul_point p q) ==>
    !a x b. m a = (x,b) ==> cs_extends a b /\
      (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> (
    rewrite_tac[compile_ecadd_points_def, compile_ecmul_point_def] >>
    ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
    >- metis_tac[abi_args_entry_alloc_buffer] >>
    rpt gen_tac >>
    rpt (FIRST [irule abi_args_entry_extends_bind,
                irule abi_args_entry_extends_ignore_bind] >> conj_tac >>
         rpt gen_tac >> BETA_TAC) >>
    simp[emit_op_labels, emit_void_labels, compile_alloc_buffer_labels,
         comp_return_def, cs_extends_refl])
QED

Theorem abi_args_entry_builtin_ecadd_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty ECAdd es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_unwrap_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_unwrap_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_ptr_val >>
  metis_tac[abi_args_entry_ec_points]
QED

Theorem abi_args_entry_builtin_ecmul_dispatch:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es a vv b.
    compile_builtin_dispatch_body cfn ce rt ty ECMul es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 4 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_unwrap_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_emitted_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> ho_match_mp_tac abi_args_entry_ptr_val >>
  metis_tac[abi_args_entry_ec_points]
QED

Theorem abi_args_entry_as_wei_decimal:
  !v scale divisor a x b.
    compile_as_wei_value_decimal v scale divisor a = (x,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  ntac 3 gen_tac >> rewrite_tac[compile_as_wei_value_decimal_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind,
              irule abi_args_entry_extends_ignore_bind] >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, emit_void_labels] >>
  Cases_on `scale = 1` >> simp[emit_op_labels] >>
  irule abi_args_entry_extends_bind >> simp[emit_op_labels]
QED

Theorem abi_args_entry_as_wei_int_scaled:
  !v scale signed. scale <> 1 ==>
    !a x b. compile_as_wei_value_int v scale signed a = (x,b) ==>
      cs_extends a b /\
      (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  rpt gen_tac >> strip_tac >> simp[compile_as_wei_value_int_def] >>
  ho_match_mp_tac abi_args_entry_emitted_prefix >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_args_entry_emit_op >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >>
  rpt (FIRST [irule abi_args_entry_extends_bind,
              irule abi_args_entry_extends_ignore_bind] >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels, emit_void_labels, comp_return_def, cs_extends_refl] >>
  Cases_on `signed` >> simp[comp_return_def, cs_extends_refl] >>
  rpt (irule abi_args_entry_extends_bind >> conj_tac >>
       rpt gen_tac >> BETA_TAC) >>
  simp[emit_op_labels]
QED

Theorem abi_args_entry_as_wei_int_safe:
  !v scale signed a x b.
    compile_as_wei_value_int v scale signed a = (x,b) ==>
      cs_extends a b /\ abi_args_entry_safe a b
Proof
  rpt gen_tac >> Cases_on `scale = 1`
  >- simp[compile_as_wei_value_int_def, comp_return_def,
          cs_extends_refl, abi_args_entry_safe_refl] >>
  metis_tac[abi_args_entry_as_wei_int_scaled, abi_args_entry_safe_def]
QED

Theorem abi_args_entry_builtin_wei_safe:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty es denom a vv b.
    compile_builtin_dispatch_body cfn ce rt ty (AsWeiValue denom) es a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_safe_pair >> conj_tac
  >- metis_tac[abi_args_entry_lower_value] >>
  gen_tac >> Cases_on `is_decimal_type (expr_type (HD es))` >> simp[] >>
  ho_match_mp_tac abi_args_entry_safe_stack_val >>
  metis_tac[abi_args_entry_as_wei_decimal, abi_args_entry_as_wei_int_safe,
            abi_args_entry_safe_def]
QED

Theorem abi_args_entry_emitted_pair_prefix:
  (!a x b. m a = (x,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) /\
  (!x b y c. k x b = (y,c) ==> cs_extends b c) ==>
  !a y c. (\(x,b). k x b) (m a) = (y,c) ==>
    cs_extends a c /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a c)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[abi_args_entry_emitted_mono, cs_extends_trans]
QED

Theorem abi_args_entry_builtin_wei_emitted:
  (!ce ty e a vv b. cfn ce ty e a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)) ==>
  !ce rt ty es denom a vv b.
    compile_builtin_dispatch_body cfn ce rt ty (AsWeiValue denom) es a = (vv,b) ==>
    cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  strip_tac >> ntac 5 gen_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  ho_match_mp_tac abi_args_entry_emitted_pair_prefix >> conj_tac
  >- metis_tac[abi_args_entry_lower_value_emitted] >>
  rpt gen_tac >> Cases_on `is_decimal_type (expr_type (HD es))` >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_stack_val rt res` >>
  Cases_on `res` >> simp[exprLoweringTheory.as_stack_val_def] >>
  strip_tac >> gvs[markerTheory.Abbrev_def] >>
  metis_tac[abi_args_entry_as_wei_decimal, abi_args_entry_as_wei_int_safe]
QED
