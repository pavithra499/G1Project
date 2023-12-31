/*
 *  This file is part of the Jikes RVM project (http://jikesrvm.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License. You
 *  may obtain a copy of the License at
 *
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  See the COPYRIGHT.txt file distributed with this work for information
 *  regarding copyright ownership.
 */
package org.jikesrvm.compilers.opt.ir.ia32;

import org.vmmagic.pragma.Pure;
import org.jikesrvm.compilers.opt.ir.Operator;

/**
 * Class to store the string representations of different operators.<p>
 * 
 * THIS FILE IS MACHINE_GENERATED. DO NOT EDIT.
 * See ArchOperatorNames.template, OperatorList.dat, etc
 */
public abstract class ArchOperatorNames {

  /** Lookup for operator names based on their opcode */
  private static final String[] operatorName = new String[] {
      "get_caught_exception    ",
      "set_caught_exception    ",
      "new                     ",
      "new_unresolved          ",
      "newarray                ",
      "newarray_unresolved     ",
      "athrow                  ",
      "checkcast               ",
      "checkcast_notnull       ",
      "checkcast_unresolved    ",
      "must_implement_interface ",
      "instanceof              ",
      "instanceof_notnull      ",
      "instanceof_unresolved   ",
      "monitorenter            ",
      "monitorexit             ",
      "newobjmultiarray        ",
      "getstatic               ",
      "putstatic               ",
      "getfield                ",
      "putfield                ",
      "int_zero_check          ",
      "long_zero_check         ",
      "bounds_check            ",
      "objarray_store_check    ",
      "objarray_store_check_notnull ",
      "ig_patch_point          ",
      "ig_class_test           ",
      "ig_method_test          ",
      "tableswitch             ",
      "lookupswitch            ",
      "int_aload               ",
      "long_aload              ",
      "float_aload             ",
      "double_aload            ",
      "ref_aload               ",
      "ubyte_aload             ",
      "byte_aload              ",
      "ushort_aload            ",
      "short_aload             ",
      "int_astore              ",
      "long_astore             ",
      "float_astore            ",
      "double_astore           ",
      "ref_astore              ",
      "byte_astore             ",
      "short_astore            ",
      "int_ifcmp               ",
      "int_ifcmp2              ",
      "long_ifcmp              ",
      "float_ifcmp             ",
      "double_ifcmp            ",
      "ref_ifcmp               ",
      "label                   ",
      "bbend                   ",
      "unint_begin             ",
      "unint_end               ",
      "fence                   ",
      "read_ceiling            ",
      "write_floor             ",
      "phi                     ",
      "split                   ",
      "pi                      ",
      "nop                     ",
      "int_move                ",
      "long_move               ",
      "float_move              ",
      "double_move             ",
      "ref_move                ",
      "guard_move              ",
      "int_cond_move           ",
      "long_cond_move          ",
      "float_cond_move         ",
      "double_cond_move        ",
      "ref_cond_move           ",
      "guard_cond_move         ",
      "guard_combine           ",
      "ref_add                 ",
      "int_add                 ",
      "long_add                ",
      "float_add               ",
      "double_add              ",
      "ref_sub                 ",
      "int_sub                 ",
      "long_sub                ",
      "float_sub               ",
      "double_sub              ",
      "int_mul                 ",
      "long_mul                ",
      "float_mul               ",
      "double_mul              ",
      "int_div                 ",
      "long_div                ",
      "unsigned_div_64_32      ",
      "unsigned_rem_64_32      ",
      "float_div               ",
      "double_div              ",
      "int_rem                 ",
      "long_rem                ",
      "float_rem               ",
      "double_rem              ",
      "ref_neg                 ",
      "int_neg                 ",
      "long_neg                ",
      "float_neg               ",
      "double_neg              ",
      "float_sqrt              ",
      "double_sqrt             ",
      "ref_shl                 ",
      "int_shl                 ",
      "long_shl                ",
      "ref_shr                 ",
      "int_shr                 ",
      "long_shr                ",
      "ref_ushr                ",
      "int_ushr                ",
      "long_ushr               ",
      "ref_and                 ",
      "int_and                 ",
      "long_and                ",
      "ref_or                  ",
      "int_or                  ",
      "long_or                 ",
      "ref_xor                 ",
      "int_xor                 ",
      "ref_not                 ",
      "int_not                 ",
      "long_not                ",
      "long_xor                ",
      "int_2addrsigext         ",
      "int_2addrze.ext         ",
      "long_2addr              ",
      "addr_2int               ",
      "addr_2long              ",
      "int_2long               ",
      "int_2float              ",
      "int_2double             ",
      "long_2int               ",
      "long_2float             ",
      "long_2double            ",
      "float_2int              ",
      "float_2long             ",
      "float_2double           ",
      "double_2int             ",
      "double_2long            ",
      "double_2float           ",
      "int_2byte               ",
      "int_2ushort             ",
      "int_2short              ",
      "long_cmp                ",
      "float_cmpl              ",
      "float_cmpg              ",
      "double_cmpl             ",
      "double_cmpg             ",
      "return                  ",
      "null_check              ",
      "goto                    ",
      "boolean_not             ",
      "boolean_cmp_int         ",
      "boolean_cmp_addr        ",
      "boolean_cmp_long        ",
      "boolean_cmp_float       ",
      "boolean_cmp_double      ",
      "byte_load               ",
      "ubyte_load              ",
      "short_load              ",
      "ushort_load             ",
      "ref_load                ",
      "ref_store               ",
      "int_load                ",
      "long_load               ",
      "float_load              ",
      "double_load             ",
      "byte_store              ",
      "short_store             ",
      "int_store               ",
      "long_store              ",
      "float_store             ",
      "double_store            ",
      "prepare_int             ",
      "prepare_addr            ",
      "prepare_long            ",
      "attempt_int             ",
      "attempt_addr            ",
      "attempt_long            ",
      "call                    ",
      "syscall                 ",
      "unimplemented_but_unreachable ",
      "yieldpoint_prologue     ",
      "yieldpoint_epilogue     ",
      "yieldpoint_backedge     ",
      "yieldpoint_osr          ",
      "osr_barrier             ",
      "ir_prologue             ",
      "resolve                 ",
      "resolve_member          ",
      "get_time_base           ",
      "instrumented_event_counter ",
      "trap_if                 ",
      "trap                    ",
      "illegal_instruction     ",
      "float_as_int_bits       ",
      "int_bits_as_float       ",
      "double_as_long_bits     ",
      "long_bits_as_double     ",
      "arraylength             ",
      "framesize               ",
      "get_obj_tib             ",
      "get_class_tib           ",
      "get_type_from_tib       ",
      "get_superclass_ids_from_tib ",
      "get_does_implement_from_tib ",
      "get_array_element_tib_from_tib ",
      "lowtableswitch          ",
      "address_constant        ",
      "int_constant            ",
      "long_constant           ",
      "register                ",
      "other_operand           ",
      "null                    ",
      "branch_target           ",
  //////////////////////////
  // END   Architecture Independent opcodes.
  // BEGIN Architecture Dependent opcodes & MIR.
  //////////////////////////
      "materialize_fp_constant ",
      "round_to_zero           ",
      "clear_floating_point_state ",
      "prefetch                ",
      "pause                   ",
      "fp_add                  ",
      "fp_sub                  ",
      "fp_mul                  ",
      "fp_div                  ",
      "fp_neg                  ",
      "fp_rem                  ",
      "int_2fp                 ",
      "long_2fp                ",
      "cmp_cmov                ",
      "fcmp_cmov               ",
      "lcmp_cmov               ",
      "cmp_fcmov               ",
      "fcmp_fcmov              ",
      "call_save_volatile      ",
      "mir_start               ",
      "require_esp             ",
      "advise_esp              ",
      "mir_lowtableswitch      ",
      "ia32_methodstart        ",
      "ia32_fclear             ",
      "dummy_def               ",
      "dummy_use               ",
      "immq_mov                ",
      "ia32_fmov_ending_live_range ",
      "ia32_fmov               ",
      "ia32_trapif             ",
      "ia32_offset             ",
      "ia32_lock_cmpxchg       ",
      "ia32_lock_cmpxchg8b     ",
      "ia32_adc                ",
      "ia32_add                ",
      "ia32_and                ",
      "ia32_bswap              ",
      "ia32_bt                 ",
      "ia32_btc                ",
      "ia32_btr                ",
      "ia32_bts                ",
      "ia32_syscall            ",
      "ia32_call               ",
      "ia32_cdq                ",
      "ia32_cdo                ",
      "ia32_cdqe               ",
      "ia32_cmov               ",
      "ia32_cmp                ",
      "ia32_cmpxchg            ",
      "ia32_cmpxchg8b          ",
      "ia32_dec                ",
      "ia32_div                ",
      "ia32_fadd               ",
      "ia32_faddp              ",
      "ia32_fchs               ",
      "ia32_fcmov              ",
      "ia32_fcomi              ",
      "ia32_fcomip             ",
      "ia32_fdiv               ",
      "ia32_fdivp              ",
      "ia32_fdivr              ",
      "ia32_fdivrp             ",
      "ia32_fexam              ",
      "ia32_fxch               ",
      "ia32_ffree              ",
      "ia32_ffreep             ",
      "ia32_fiadd              ",
      "ia32_fidiv              ",
      "ia32_fidivr             ",
      "ia32_fild               ",
      "ia32_fimul              ",
      "ia32_finit              ",
      "ia32_fist               ",
      "ia32_fistp              ",
      "ia32_fisub              ",
      "ia32_fisubr             ",
      "ia32_fld                ",
      "ia32_fldcw              ",
      "ia32_fld1               ",
      "ia32_fldl2t             ",
      "ia32_fldl2e             ",
      "ia32_fldpi              ",
      "ia32_fldlg2             ",
      "ia32_fldln2             ",
      "ia32_fldz               ",
      "ia32_fmul               ",
      "ia32_fmulp              ",
      "ia32_fnstcw             ",
      "ia32_fnstsw             ",
      "ia32_fninit             ",
      "ia32_fnsave             ",
      "ia32_fprem              ",
      "ia32_frstor             ",
      "ia32_fst                ",
      "ia32_fstcw              ",
      "ia32_fstsw              ",
      "ia32_fstp               ",
      "ia32_fsub               ",
      "ia32_fsubp              ",
      "ia32_fsubr              ",
      "ia32_fsubrp             ",
      "ia32_fucomi             ",
      "ia32_fucomip            ",
      "ia32_idiv               ",
      "ia32_imul1              ",
      "ia32_imul2              ",
      "ia32_inc                ",
      "ia32_int                ",
      "ia32_jcc                ",
      "ia32_jcc2               ",
      "ia32_jmp                ",
      "ia32_lea                ",
      "ia32_lock               ",
      "ia32_mov                ",
      "ia32_movzx__b           ",
      "ia32_movsx__b           ",
      "ia32_movzx__w           ",
      "ia32_movsx__w           ",
      "ia32_movzxq__b          ",
      "ia32_movsxq__b          ",
      "ia32_movzxq__w          ",
      "ia32_movsxq__w          ",
      "ia32_movsxdq            ",
      "ia32_mul                ",
      "ia32_neg                ",
      "ia32_not                ",
      "ia32_or                 ",
      "ia32_mfence             ",
      "ia32_pause              ",
      "ia32_ud2                ",
      "ia32_prefetchnta        ",
      "ia32_pop                ",
      "ia32_push               ",
      "ia32_rcl                ",
      "ia32_rcr                ",
      "ia32_rol                ",
      "ia32_ror                ",
      "ia32_ret                ",
      "ia32_sal                ",
      "ia32_sar                ",
      "ia32_shl                ",
      "ia32_shr                ",
      "ia32_sbb                ",
      "ia32_set__b             ",
      "ia32_shld               ",
      "ia32_shrd               ",
      "ia32_sub                ",
      "ia32_test               ",
      "ia32_xor                ",
      "ia32_rdtsc              ",
      "ia32_addss              ",
      "ia32_subss              ",
      "ia32_mulss              ",
      "ia32_divss              ",
      "ia32_addsd              ",
      "ia32_subsd              ",
      "ia32_mulsd              ",
      "ia32_divsd              ",
      "ia32_andps              ",
      "ia32_andpd              ",
      "ia32_andnps             ",
      "ia32_andnpd             ",
      "ia32_orps               ",
      "ia32_orpd               ",
      "ia32_xorps              ",
      "ia32_xorpd              ",
      "ia32_ucomiss            ",
      "ia32_ucomisd            ",
      "ia32_cmpeqss            ",
      "ia32_cmpltss            ",
      "ia32_cmpless            ",
      "ia32_cmpunordss         ",
      "ia32_cmpness            ",
      "ia32_cmpnltss           ",
      "ia32_cmpnless           ",
      "ia32_cmpordss           ",
      "ia32_cmpeqsd            ",
      "ia32_cmpltsd            ",
      "ia32_cmplesd            ",
      "ia32_cmpunordsd         ",
      "ia32_cmpnesd            ",
      "ia32_cmpnltsd           ",
      "ia32_cmpnlesd           ",
      "ia32_cmpordsd           ",
      "ia32_movapd             ",
      "ia32_movaps             ",
      "ia32_movlpd             ",
      "ia32_movlps             ",
      "ia32_movss              ",
      "ia32_movsd              ",
      "ia32_movd               ",
      "ia32_movq               ",
      "ia32_psllq              ",
      "ia32_psrlq              ",
      "ia32_sqrtss             ",
      "ia32_sqrtsd             ",
      "ia32_cvtsi2ss           ",
      "ia32_cvtss2sd           ",
      "ia32_cvtss2si           ",
      "ia32_cvttss2si          ",
      "ia32_cvtsi2sd           ",
      "ia32_cvtsd2ss           ",
      "ia32_cvtsd2si           ",
      "ia32_cvttsd2si          ",
      "ia32_cvtsi2sdq          ",
      "ia32_cvtsd2siq          ",
      "ia32_cvttsd2siq         ",
      "mir_end                 ",
      "<UNKNOWN OPERATOR>"
    };

  /**
   * Looks up name of operator
   * @param operator the operator to look up
   * @return operator's name or a string indicating
   *  that the operator isn't known
   */
  @Pure
  public static String toString(Operator operator) {
     try {
       return operatorName[operator.getOpcode()];
     }
     catch (ArrayIndexOutOfBoundsException e) {
       return operatorName[operatorName.length-1];
     }
  }
}
