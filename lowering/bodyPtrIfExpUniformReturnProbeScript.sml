Theory bodyPtrIfExpUniformReturnProbe
Ancestors
  bodyPtrIfExpHeaderProbe

(* Finite fragment experiments only: neither initial state is asserted to
   satisfy a complete module's body frame or ghost invariant. *)
Theorem header_probe_zero_physical_run:
  !ce. case run_inst_seq
    ((SND (lower_value compile_expr ce header_probe_ty header_probe_expr
      (initial_compile_state "entry"))).cs_current_insts ++
     [mk_inst 13 MCOPY [Lit 256w; Var "%0"; Lit 128w] []])
    ((init_venom_state "entry") with vs_memory := REPLICATE 256 0w) of
    OK s => val_in_memory
      (TupleTV [BaseTV (BytesT (Dynamic 32));
                ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
      (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 256 s.vs_memory
  | _ => F
Proof
  rewrite_tac[header_probe_compile] >>
  simp[integer_wordTheory.i2w_def] >>
  CONV_TAC (computeLib.CBV_CONV
    (computeLib.add_thms [integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def]
      (wordsLib.add_words_compset true
        (computeLib.copy (computeLib.the_compset())))))
QED

Theorem header_probe_uniform_physical_run:
  !ce s.
    (s = ((init_venom_state "entry") with vs_memory := REPLICATE 256 0w) \/
     s = ((init_venom_state "entry") with vs_memory := REPLICATE 256 1w)) ==>
    case run_inst_seq
      ((SND (lower_value compile_expr ce header_probe_ty header_probe_expr
        (initial_compile_state "entry"))).cs_current_insts ++
       [mk_inst 13 MCOPY [Lit 256w; Var "%0"; Lit 128w] []]) s of
      OK t => val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 32));
                  ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
        (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 256 t.vs_memory
    | _ => F
Proof
  rpt strip_tac >> gvs[]
  >- simp[header_probe_zero_physical_run] >>
  qspec_then `ce` mp_tac header_probe_return_run >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code state` >>
  Cases_on `run_inst_seq code state` >> simp[]
QED

Theorem header_probe_not_uniform_annotation_run:
  !ce. ~(!s.
    (s = ((init_venom_state "entry") with vs_memory := REPLICATE 256 0w) \/
     s = ((init_venom_state "entry") with vs_memory := REPLICATE 256 1w)) ==>
    case run_inst_seq
      ((SND (lower_value compile_expr ce header_probe_ty header_probe_expr
        (initial_compile_state "entry"))).cs_current_insts ++
       [mk_inst 13 MCOPY [Lit 256w; Var "%0"; Lit 128w] []]) s of
      OK t => val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 64));
                  ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
        (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 256 t.vs_memory
    | _ => F)
Proof
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then
    `(init_venom_state "entry") with vs_memory := REPLICATE 256 1w` mp_tac) >>
  simp[] >>
  qspec_then `ce` mp_tac header_probe_return_run >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code state` >>
  Cases_on `run_inst_seq code state` >> simp[]
QED
