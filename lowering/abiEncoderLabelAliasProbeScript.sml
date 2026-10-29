(* Checked label-alias diagnostics; no compiler well-formedness assumption. *)
Theory abiEncoderLabelAliasProbe
Ancestors
  abiEncoder compileEnv fragExec emitHelper venomInst venomState
  abiEncoderLeafSafety abiEncoderObserver
  venomExecSemantics list rich_list arithmetic

Definition alias_base_def:
  alias_base = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
    cs_current_bb := fresh_label_output "enc_dyn_exit" 2;
    cs_current_insts := []; cs_blocks := []; cs_data_sections := []|>
End

Definition alias_compile_def:
  alias_compile = compile_abi_encode_dyn_static_loop
    (Lit 0w) (Lit 64w) AbiPrimWord 32 32 (Lit 0w)
End

Definition alias_old_def:
  alias_old = (SND (alias_compile alias_base)).cs_current_insts
End

Definition alias_start_def:
  alias_start = alias_base with cs_current_insts := alias_old
End

Definition alias_end_def:
  alias_end = SND (alias_compile alias_start)
End

Definition alias_function_def:
  alias_function (fn:ir_function) = fn with fn_blocks :=
    alias_end.cs_blocks ++
    [<|bb_label := alias_end.cs_current_bb;
       bb_instructions := alias_end.cs_current_insts ++ [mk_inst 100 STOP [] []]|>]
End

Theorem alias_entry_exit_equal:
  alias_start.cs_current_bb = alias_end.cs_current_bb /\
  LENGTH alias_start.cs_current_insts = 3 /\
  LENGTH alias_end.cs_current_insts = 3
Proof
  EVAL_TAC
QED

Theorem alias_containing_function:
  fn_has_code alias_start alias_end (alias_function fn)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem alias_first_cut_trivial:
  s.vs_current_bb = alias_start.cs_current_bb /\
  s.vs_inst_idx = LENGTH alias_start.cs_current_insts /\
  local_prefix ctx fn (alias_end.cs_current_bb,LENGTH alias_end.cs_current_insts) s t ==>
  t = s
Proof
  strip_tac >> mp_tac alias_entry_exit_equal >> strip_tac >>
  irule local_prefix_at_cut >> gvs[] >> metis_tac[]
QED

Definition alias_entry_block_def:
  alias_entry_block = EL 2 alias_end.cs_blocks
End

Theorem alias_entry_emitted:
  MEM alias_entry_block (emitted_blocks alias_start alias_end) /\
  alias_entry_block.bb_label = alias_end.cs_current_bb /\
  get_instruction alias_entry_block (LENGTH alias_end.cs_current_insts) =
    SOME (mk_inst 0 ALLOCA [Lit 32w] ["%0"])
Proof
  EVAL_TAC
QED

Theorem alias_no_stop_observer:
  fn_has_code alias_start alias_end observed ==>
  ~observer_region_safe observed
     (alias_end.cs_current_bb,LENGTH alias_end.cs_current_insts) R
Proof
  simp_tac bool_ss [fn_has_code_def, observer_region_safe_def] >>
  strip_tac >> disj1_tac >> qexists_tac `alias_entry_block` >>
  mp_tac alias_entry_emitted >> strip_tac >>
  qpat_x_assum `!bb. MEM bb _ ==> _`
    (qspec_then `alias_entry_block` mp_tac) >>
  simp[] >> strip_tac >> gvs[mk_inst_def]
QED

Theorem alias_compile_equation:
  compile_abi_encode_dyn_static_loop (Lit 0w) (Lit 64w)
    AbiPrimWord 32 32 (Lit 0w) alias_start = (Var "%15",alias_end)
Proof
  EVAL_TAC
QED
