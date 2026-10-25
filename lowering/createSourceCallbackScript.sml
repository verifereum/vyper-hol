Theory createSourceCallback
Ancestors
  list rich_list createFrameInterface vyperInterpreter compileEnv valueEncoding
  vyperState vyperValueOperation venomState venomExecSemantics

(* These are conditional specifications, not compiler simulation theorems.
   In particular compile_expr_correct is neither imported as a premise nor used.
   Word callbacks describe lower_value; located callbacks describe a memory
   pointer with the existing typed value layout, never val_to_w256 of a tuple. *)
Datatype:
  create_callback_rep = CreateWord | CreateMemory type_value
End

Definition create_callback_word_def:
  create_callback_word v op s <=>
    (case v of
       BoolV _ => T | IntV _ => T | FlagV _ => T | DecimalV _ => T
     | BytesV bs => LENGTH bs <= 32 | _ => F) /\
    eval_operand op s = SOME (val_to_w256 v)
End

Definition create_callback_represents_def:
  create_callback_represents CreateWord v op s =
    create_callback_word v op s /\
  create_callback_represents (CreateMemory tv) v op s =
    (?ptr. eval_operand op s = SOME ptr /\
           val_in_memory tv v (w2n ptr) s.vs_memory)
End

(* A saved slice is (byte offset, exact saved bytes). Its length, including
   zero-length slices, is explicit. Source/target state_rel supplies no such
   private-memory guarantee. *)
Definition create_memory_snapshot_def:
  create_memory_snapshot regions s <=>
    EVERY (\(offset,bs). TAKE (LENGTH bs) (DROP offset s.vs_memory) = bs) regions
End

Definition create_source_entry_def:
  create_source_entry func cenv cx es cs s <=>
    state_rel func cenv cx es s /\ fresh_vars_wrt cs s
End

Definition create_source_normal_def:
  create_source_normal func cenv cx e es rep op cs s <=>
    ?v es'. eval_expr cx e es = (INL (Value v),es') /\
      state_rel func cenv cx es' s /\ create_callback_represents rep v op s /\
      fresh_vars_wrt cs s
End

(* Only expression exceptions can exit here. Runtime/type errors correspond
   to an empty-data revert, raw revert data must match exactly. The special
   unreachable assertion may additionally halt exceptionally. This contract
   deliberately does not relate Return/Break/Continue or arbitrary target exits.
   It does not require source-state/private-frame preservation after an abort. *)
Definition create_exception_matches_def:
  create_exception_matches ex r <=>
    case (ex,r) of
      (Error (RevertData bs), Abort Revert_abort s) => s.vs_returndata = bs
    | (Error (RuntimeError msg), Abort Revert_abort s) => s.vs_returndata = []
    | (Error (TypeError msg), Abort Revert_abort s) => s.vs_returndata = []
    | (AssertException msg, Abort Revert_abort s) => s.vs_returndata = []
    | (AssertException msg, Abort ExHalt_abort s) => msg = "UNREACHABLE"
    | _ => F
End

Definition create_source_exit_def:
  create_source_exit cx e es r <=>
    ?ex es'. eval_expr cx e es = (INR ex,es') /\ create_exception_matches ex r
End

Definition create_source_callback_spec_def:
  create_source_callback_spec ctx func cenv cx e es rep callback live regions <=>
    create_callback_spec ctx callback
      (create_source_entry func cenv cx es)
      (create_source_normal func cenv cx e es rep)
      (create_source_exit cx e es) live (create_memory_snapshot regions)
End

Theorem create_source_callback_specialization:
  create_source_callback_spec ctx func cenv cx e es rep callback live regions <=>
  !cs op cs'. callback cs = (op,cs') ==>
    cs_extends cs cs' /\
    frag_exec ctx cs cs'
      (\s. state_rel func cenv cx es s /\ fresh_vars_wrt cs s /\
           create_live live s /\ create_memory_snapshot regions s)
      (\s. create_source_normal func cenv cx e es rep op cs' s /\
           create_live live s /\ create_memory_snapshot regions s)
      (create_source_exit cx e es)
Proof
  simp[create_source_callback_spec_def, create_callback_spec_def,
       create_source_entry_def, CONJ_ASSOC]
QED

Theorem create_source_normal_projection:
  create_source_normal func cenv cx e es rep op cs s /\
  create_live live s /\ create_memory_snapshot regions s ==>
  ?v es'. eval_expr cx e es = (INL (Value v),es') /\
    state_rel func cenv cx es' s /\ create_callback_represents rep v op s /\
    fresh_vars_wrt cs s /\ create_live live s /\
    create_memory_snapshot regions s
Proof
  simp[create_source_normal_def] >> metis_tac[]
QED

Theorem create_source_exit_projection:
  create_source_exit cx e es r ==>
  ?ex es'. eval_expr cx e es = (INR ex,es') /\ create_exception_matches ex r
Proof
  simp[create_source_exit_def]
QED

Theorem create_normal_excludes_exit:
  eval_expr cx e es = (INL tv,es') ==> ~create_source_exit cx e es r
Proof
  simp[create_source_exit_def]
QED

Theorem create_exception_excludes_normal:
  eval_expr cx e es = (INR ex,es') ==>
  ~create_source_normal func cenv cx e es rep op cs s
Proof
  simp[create_source_normal_def]
QED

Theorem create_revert_data_exact:
  create_exception_matches (Error (RevertData bs)) (Abort a s) <=>
    a = Revert_abort /\ s.vs_returndata = bs
Proof
  Cases_on `a` >> simp[create_exception_matches_def]
QED

Theorem create_exit_rejects_halt:
  ~create_source_exit cx e es (Halt s)
Proof
  simp[create_source_exit_def, create_exception_matches_def] >>
  Cases_on `ex` >> simp[]
QED

Theorem create_memory_snapshot_trans:
  create_memory_snapshot regions s1 /\ create_memory_snapshot regions s2 ==>
  EVERY (\(offset,bs). TAKE (LENGTH bs) (DROP offset s1.vs_memory) =
                       TAKE (LENGTH bs) (DROP offset s2.vs_memory)) regions
Proof
  simp[create_memory_snapshot_def, EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `(e0,e1)` mp_tac) >> simp[]
QED

Theorem create_word_projection:
  create_callback_represents CreateWord v op s ==>
  eval_operand op s = SOME (val_to_w256 v)
Proof
  simp[create_callback_represents_def, create_callback_word_def]
QED

Theorem create_located_projection:
  create_callback_represents (CreateMemory tv) v op s ==>
  ?ptr. eval_operand op s = SOME ptr /\
        val_in_memory tv v (w2n ptr) s.vs_memory
Proof
  simp[create_callback_represents_def]
QED

(* Discrimination probes: composites cannot masquerade as scalar zero,
   a failed create cannot discard its revert payload, and a snapshot must
   actually contain its bytes (not merely a source-related state). *)
Theorem create_tuple_not_word:
  ~create_callback_represents CreateWord (ArrayV (TupleV vs)) op s
Proof
  simp[create_callback_represents_def, create_callback_word_def]
QED

Theorem create_wrong_revert_data_rejected:
  s.vs_returndata <> bs ==>
  ~create_exception_matches (Error (RevertData bs)) (Abort Revert_abort s)
Proof
  simp[create_exception_matches_def]
QED

Theorem create_memory_snapshot_projection:
  create_memory_snapshot regions s /\ MEM (offset,bs) regions ==>
  TAKE (LENGTH bs) (DROP offset s.vs_memory) = bs
Proof
  simp[create_memory_snapshot_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(offset,bs)` mp_tac) >> simp[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createSourceCallback");
