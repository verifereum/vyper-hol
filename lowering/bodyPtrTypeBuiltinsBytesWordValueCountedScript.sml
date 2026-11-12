Theory bodyPtrTypeBuiltinsBytesWordValueCounted
Ancestors
  bodyPtrTypeBuiltinsBytesWordCounted bodyPtrSignedConvertUnsignedValue
  bodyPtrTypeBuiltinsUintCounted bodyPtrDefs
  exprLowering exprLoweringProps compileEnv venomState finite_map arithmetic

(* Source constructors share the same footprint contract, not the same value. *)
Theorem bytes_word_value_counted_success:
  (conv = ConvBytestringToBool \/ (?m. conv = ConvBytestringToBytesM m) \/
   (?b cap. conv = ConvBytestringToInt F b cap)) /\
  compile_type_convert (Var src) conv sa = (out,sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\ lookup_var src s = SOME a /\
  ptr_mem_ok cx (expr_type e) v (Var src) G tn s /\
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ((?bs. v = BytesV bs /\ n = LENGTH bs /\ tv <> BaseTV AddressT /\
     (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v = StringV str /\ n = LENGTH str)) /\
  n <= 32 /\ 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  w2n a+32 < dimword(:256) /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
   mload (w2n a) s = n2w n /\
   (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem)` by
    (qpat_x_assum `(?bs. v = BytesV bs /\ _) \/ _` strip_assume_tac
     >- (gvs[] >> drule_all unsigned_bytes_value_source_facts >> simp[]) >>
     gvs[] >> drule_all unsigned_string_value_source_facts >> simp[]) >>
  irule bytes_word_counted_success >> metis_tac[]
QED
