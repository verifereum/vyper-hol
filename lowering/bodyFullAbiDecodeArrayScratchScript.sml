Theory bodyFullAbiDecodeArrayScratch
Ancestors
  bodyFullAbiDecodeDecoderFrame bodyFullAbiDecodeStoreContents
  bodyFullAbiDecodeInputOrigin bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeInterface bodyPtrIfExpAllocSeparation
  assignBasePtrLiteralGhost loweringHalt exprLoweringProps
  finite_map words list pair arithmetic

(* Separate the actual allocation site, not the allocation frontier.  The
   two alternatives for the input certificate are deliberately retained. *)
Theorem abi_decode_scratch_actual_separation[local]:
  stmt_state_rel H ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w 32)] [out]) (fn_insts fn) /\
  not_local_ptr ce es.scopes out /\ output_id < id /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  ((?aid ib isz. aid < output_id /\
      FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
      ib <= w2n (input_word:256 word) /\
      w2n input_word + LENGTH (input_bytes:8 word list) <= ib+isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
      ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib+isz)) /\
  EVERY (\(a,bytes:8 word list). output_base <= a /\
    a+LENGTH bytes <= output_base+output_cap) protected ==>
  (output_base+output_cap <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= output_base) /\
  (w2n input_word+LENGTH input_bytes <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= w2n input_word) /\
  EVERY (\(a,bytes). a+LENGTH bytes <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= a) protected /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= buffer_allocation_base s id \/ buffer_allocation_base s id+32 <= b)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `output_id <> id` by decide_tac >>
  `output_base+output_cap <= buffer_allocation_base s id \/
    buffer_allocation_base s id+32 <= output_base` by
    (irule ifexp_alloca_old_site_separate >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (gvs[] >>
      imp_res_tac ifexp_alloca_old_site_separate >>
      imp_res_tac ifexp_alloca_local_separate >> decide_tac) >>
  conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      PairCases_on `e` >> gvs[] >>
      first_x_assum drule >> simp[] >> decide_tac) >>
  metis_tac[ifexp_alloca_local_separate]
QED
