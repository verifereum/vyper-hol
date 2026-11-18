(*
 * Statement simulation: a declared local's store, for any one-word value
 * (#637)
 *
 * loweringSlice's stmt_state_rel_declare_word stores val_to_w256 v of a
 * word_value v; a local of an address or bytesN type stores its typed word
 * typed_val_to_w256 instead, which val_in_memory lays out the same way.
 * loweringSlice's stmt_state_rel_declare_store takes the stored word and the
 * value's layout as premises, so both kinds of locals use it.
 *
 * TOP-LEVEL:
 *   store_lays_out               — the stored word lays out the value
 *   store_lays_out_word_value, store_lays_out_typed — its two sources
 *   store_lays_out_memory_value_rel — the store's complete layout
 *   typed_word_store             — a typed value of a word type is laid out
 *                                  by its typed word, and well formed
 *)

Theory stmtSimDeclStore
Ancestors
  exprSimProps
  list rich_list finite_map pred_set
  fragExec localPtrsProps venomMemDefs loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperTyping
  venomExecSemantics venomInst venomState

(* A value of a word type, of that type: its typed word lays it out, and
   it is well formed in one word. *)
Theorem typed_word_store:
  !tenv t tyv v off s.
    is_word_type t /\ evaluate_type tenv t = SOME tyv /\
    value_has_type tyv v ==>
    val_in_memory tyv v off
      (mstore off (typed_val_to_w256 tyv v) s).vs_memory /\
    val_wf tyv v /\ type_memory_size tyv = 32
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def,
      val_wf_def, type_memory_size_def, mstore_mem_word_at_same]
QED

(* The value v of a declared local of type tyv, from a right-hand side of
   type etv whose operand holds typed_val_to_w256 etv v: storing that word
   lays v out, in one word. *)
Definition store_lays_out_def:
  store_lays_out etv tyv v <=>
    val_wf tyv v /\ type_memory_size tyv = 32 /\ word_memory_type tyv /\
    !off s. val_in_memory tyv v off
              (mstore off (typed_val_to_w256 etv v) s).vs_memory
End

Theorem store_lays_out_word_value:
  !tenv t etv tyv v.
    word_value v /\ type_memory_size tyv = 32 /\ word_memory_type tyv /\
    is_word_type t /\ evaluate_type tenv t = SOME etv ==>
    store_lays_out etv tyv v
Proof
  rpt strip_tac >>
  `typed_val_to_w256 etv v = val_to_w256 v` by
    simp[typed_val_to_w256_word_value] >>
  simp[store_lays_out_def, word_value_in_memory, word_value_wf]
QED

Theorem store_lays_out_typed:
  !tenv t tyv v.
    is_word_type t /\ evaluate_type tenv t = SOME tyv /\
    value_has_type tyv v ==>
    store_lays_out tyv tyv v
Proof
  rpt strip_tac >> simp[store_lays_out_def] >>
  metis_tac[typed_word_store, evaluate_word_memory_type]
QED

(* The stored word also gives the local's complete layout, which
   local_ptrs_rel keeps for every live local. *)
Theorem store_lays_out_memory_value_rel:
  !etv tyv v off s.
    store_lays_out etv tyv v ==>
    memory_value_rel tyv v off
      (mstore off (typed_val_to_w256 etv v) s).vs_memory
Proof
  rw[store_lays_out_def, word_memory_type_memory_value_rel]
QED
