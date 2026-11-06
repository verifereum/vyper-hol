Theory concretizePtrPairedCallSchema
Ancestors
  concretizePtrPairedCallEntry concretizePtrPairedPrefixProbe
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrDeletedGapHistory venomExecSemantics venomWf unitShapeDefs
  ptrDiscipline finite_map list

(* Specification audit only: no theorem, axiom or new constant. *)
val _ = type_of ``
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  decode_invoke at.po_inst = SOME (nm,ops) /\
  eval_operands ops at.po_state = SOME argst /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  lookup_function nm Ct.ctx_functions = SOME g /\
  active_inst at.po_fn at.po_inst at.po_state /\
  setup_callee g argst at.po_state = SOME ct /\ enters_block g ct ct' /\
  active_inst g it ct' /\
  bt = ptr_observe
    (<|cf_fn := at.po_fn; cf_inst := at.po_inst; cf_state := at.po_state;
       cf_params := at.po_params; cf_prov := at.po_prov;
       cf_tvar := at.po_taint.t_var|> :: at.po_stack)
    (MAP (op_prov at.po_prov) ops) FEMPTY
    (at.po_taint with t_var := FEMPTY) g it ct' /\
  ptr_chrono_step Ct at bt ==>
  ?f args cs cs' i b B bb n delta snapshots.
    lookup_function nm C.ctx_functions = SOME f /\
    eval_operands ops a.po_state = SOME args /\
    setup_callee f args a.po_state = SOME cs /\ enters_block f cs cs' /\
    active_inst f i cs' /\
    b = ptr_observe
      (<|cf_fn := a.po_fn; cf_inst := a.po_inst; cf_state := a.po_state;
         cf_params := a.po_params; cf_prov := a.po_prov;
         cf_tvar := a.po_taint.t_var|> :: a.po_stack)
      (MAP (op_prov a.po_prov) ops) FEMPTY
      (a.po_taint with t_var := FEMPTY) f i cs' /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved) /\
    B = ptr_birth_overlay (LENGTH h) b.po_state.vs_allocas births /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
      (LENGTH h :: tokens) (registry |+ (LENGTH h,f)) B
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)
      (entries |+ (LENGTH h,LENGTH ht))
      (H ++ [(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
        MAP (op_prov TG) ops,FEMPTY,((PT,TG)::saved),
        entries |+ (LENGTH h,LENGTH ht))])
      ((LENGTH h - 1,LENGTH ht - 1)::calls) ws /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1])
      (LENGTH h :: tokens) (registry |+ (LENGTH h,f)) B
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)
      (entries |+ (LENGTH h,LENGTH ht))
      ((H ++ [(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
        MAP (op_prov TG) ops,FEMPTY,((PT,TG)::saved),
        entries |+ (LENGTH h,LENGTH ht))]) ++ snapshots)
      ((LENGTH h - 1,LENGTH ht - 1)::calls) ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp f)
      (ptr_gap_scan bb n b).po_inst
``;
