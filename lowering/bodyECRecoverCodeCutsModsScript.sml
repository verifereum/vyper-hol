(* Paired compiler cuts for the linked ECRecover fragment.  The
   semantic frame and the generated-GAS site are handled by the callers;
   this satellite only exposes the fixed compiler decomposition. *)
Theory bodyECRecoverCodeCutsMods
Ancestors
  bodyPtrPrecompileBuiltinsCompilerStages
  gasShadowCompileBuiltinScalar gasShadowState
  exprLoweringProps compileEnv
  vyperAST
Libs
  monadsyntax
Theorem ecrecover_code_cuts_mods:
  compile_ecrecover h v r sig sf = (res,sb) /\
  compile_ecrecover h v r sig shadow_sf = (res,shadow_sb) /\
  gas_shadow_state sf shadow_sf ==>
  (?ib sa s0 s1 s2 sp ob so sm.
     compile_alloc_buffer 128 sf = (ib,sa) /\
     emit_void MSTORE [ib.buf_operand; h] sa = ((),s0) /\
     (do dst <- emit_op ADD [ib.buf_operand; Lit 32w];
         emit_void MSTORE [dst; v] od) s0 = ((),s1) /\
     (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
         emit_void MSTORE [dst; r] od) s1 = ((),s2) /\
     (do dst <- emit_op ADD [ib.buf_operand; Lit 96w];
         emit_void MSTORE [dst; sig] od) s2 = ((),sp) /\
     compile_alloc_buffer 32 sp = (ob,so) /\
     emit_void MSTORE [ob.buf_operand; Lit 0w] so = ((),sm) /\
     comp_bind
       (do gas <- emit_op GAS [];
           success <- emit_op STATICCALL
             [gas; Lit 1w; ib.buf_operand; Lit 128w;
              ob.buf_operand; Lit 32w];
           emit_void ASSERT [success];
           return ob.buf_operand od)
       (\out. emit_op MLOAD [out]) sm = (res,sb)) /\
  (?shib sha0 sh0 sh1 sh2 shp shob sho shm.
     compile_alloc_buffer 128 shadow_sf = (shib,sha0) /\
     emit_void MSTORE [shib.buf_operand; h] sha0 = ((),sh0) /\
     (do dst <- emit_op ADD [shib.buf_operand; Lit 32w];
         emit_void MSTORE [dst; v] od) sh0 = ((),sh1) /\
     (do dst <- emit_op ADD [shib.buf_operand; Lit 64w];
         emit_void MSTORE [dst; r] od) sh1 = ((),sh2) /\
     (do dst <- emit_op ADD [shib.buf_operand; Lit 96w];
         emit_void MSTORE [dst; sig] od) sh2 = ((),shp) /\
     compile_alloc_buffer 32 shp = (shob,sho) /\
     emit_void MSTORE [shob.buf_operand; Lit 0w] sho = ((),shm) /\
     comp_bind
       (do gas <- emit_op GAS [];
           success <- emit_op STATICCALL
             [gas; Lit 1w; shib.buf_operand; Lit 128w;
              shob.buf_operand; Lit 32w];
           emit_void ASSERT [success];
           return shob.buf_operand od)
       (\out. emit_op MLOAD [out]) shm = (res,shadow_sb))
Proof
  strip_tac >>
  conj_tac
  >- metis_tac[recovery_compiler_stages]
  >- metis_tac[recovery_compiler_stages]
QED
