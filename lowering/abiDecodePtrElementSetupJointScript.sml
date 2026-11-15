(* Static array element setup reuses the canonical opcode-independent path. *)
Theory abiDecodePtrElementSetupJoint
Ancestors
  decoderArraySetupPtr abiDecoderStaticLoopSetup abiDecodePtrMemberFrame
  ghostPcTransportPtr abiDecoderLoopSetup abiDecoderIndexedAddress
  loweringStateRelDefs abiEncoder compileEnv emitHelperProps exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  finite_map words arithmetic list

(* Static-element branch only; relative base/hi do not emit instructions here. *)
Theorem abi_decode_static_element_setup_success_joint:
  ~dec_info_needs_offset di /\
  abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
    (Var source) hi di abi_sz mem_sz st = (ops,ready) /\
  fn_has_code st ready func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn index s 32 /\ lookup_var index s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  mload slot s = n2w j /\ j < dimword (:256) /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s cap /\
  32+j*mem_sz+mem_sz <= cap /\ d+cap < dimword (:256) /\
  not_fresh_at st index /\ not_fresh_at st root /\ not_fresh_at st source /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  allocas_from lo s /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  ?G' tn' child.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')) /\
    SND (SND ops) = Var child /\ ptr_covers G' tn' child t mem_sz /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    ptr_covers G' tn' index t 32 /\ ptr_covers G' tn' root t cap /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `abi_decode_array_element_setup (Var index) pos (Var root) MLOAD
     (Var source) hi di abi_sz mem_sz =
   abi_decode_array_element_setup (Var index) pos (Var root) CALLDATALOAD
     (Lit 0w) (Lit 0w) di abi_sz mem_sz` by
    simp[abi_decode_array_element_setup_def] >>
  `abi_decode_array_element_setup (Var index) pos (Var root) CALLDATALOAD
     (Lit 0w) (Lit 0w) di abi_sz mem_sz st = (ops,ready)` by metis_tac[] >>
  `d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256)` by decide_tac >>
  mp_tac (calldata_array_element_setup_endpoint_ptr_origin_core |> Q.SPECL
    [`index`, `pos`, `root`, `di`, `abi_sz`, `mem_sz`, `st`, `ops`, `ready`,
     `s`, `slot`, `j`, `p`, `G`, `tn`, `d`, `cap`, `t`, `ARB`, `ctx`, `PG`, `ARB`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),HG,u)` by
    (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  `abi_decode_ptr_window HG u t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  `ptr_covers HG u index t 32 /\ ptr_covers HG u root t cap` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl_tac [`HG`, `u`, `child`] >>
  fs[ptr_covers_inst_idx]
QED
