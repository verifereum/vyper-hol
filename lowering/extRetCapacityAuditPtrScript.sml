(* Checked local witnesses for the declared-capacity audit, not frame counterexamples. *)
Theory extRetCapacityAuditPtr
Ancestors
  compileVyper compileEnv supportedTypes vyperTypeABI loweringPosts
  vyperTyping words arithmetic
val _ = Parse.hide "body";

Theorem singleton_huge_capacity_witness:
  supported_string_type (BaseT (BytesT (Dynamic (dimword(:256))))) /\
  supported_string_type (BaseT (StringT (dimword(:256)))) /\
  val_footprint (BaseTV (BytesT (Dynamic (dimword(:256))))) (BytesV []) = 32 /\
  64 + ceil32 (dimword(:256)) > dimword(:256) /\
  (n2w (64 + ceil32 (dimword(:256))) : bytes32) = 64w
Proof
  simp[dimword_def] >> EVAL_TAC
QED

Theorem singleton_boundary_capacity_witness:
  supported_string_type (BaseT (BytesT (Dynamic (dimword(:256) - 64)))) /\
  val_footprint (BaseTV (BytesT (Dynamic (dimword(:256) - 64)))) (BytesV []) = 32 /\
  64 + ceil32 (dimword(:256) - 64) = dimword(:256) /\
  (n2w (64 + ceil32 (dimword(:256) - 64)) : bytes32) = 0w
Proof
  simp[dimword_def] >> EVAL_TAC
QED

Theorem external_return_buffer_guard_without_valued_return:
  ~stmts_valued_return body ==>
  external_return_buffer_ok
    (lbl,cenv,pos,cds,payable,nr,nkey,ut,view,body,SOME ret)
Proof
  simp[external_return_buffer_ok_def]
QED

Theorem external_return_buffer_guard_strict_bound:
  external_return_buffer_ok
    (lbl,cenv,pos,cds,payable,nr,nkey,ut,view,body,SOME ret) /\
  ~cenv.ce_raw_return /\ ~is_word_type ret /\ stmts_valued_return body ==>
  cenv.ce_max_return_size < dimword(:256)
Proof
  rw[external_return_buffer_ok_def, return_buffer_ok_def, dimword_def] >>
  gvs[] >> decide_tac
QED

Theorem singleton_boundary_alloca_literal:
  mk_inst id ALLOCA
    [Lit (n2w (64 + ceil32 (dimword(:256) - 64)))] [out] =
  mk_inst id ALLOCA [Lit 0w] [out]
Proof
  simp[singleton_boundary_capacity_witness]
QED

Theorem huge_capacity_guard_vacuous_witness:
  external_return_buffer_ok
    (lbl,cenv with ce_max_return_size := dimword(:256),pos,cds,
     payable,nr,nkey,ut,view,[],SOME (BaseT (BytesT (Dynamic (dimword(:256) - 64))))) /\
  ~return_buffer_ok (cenv with ce_max_return_size := dimword(:256))
Proof
  simp[external_return_buffer_ok_def, stmt_valued_return_def,
       return_buffer_ok_def, dimword_def]
QED
