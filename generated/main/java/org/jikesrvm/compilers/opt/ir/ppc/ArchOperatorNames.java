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
package org.jikesrvm.compilers.opt.ir.ppc;

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
      "dcbf                    ",
      "dcbst                   ",
      "dcbt                    ",
      "dcbtst                  ",
      "dcbz                    ",
      "dcbzl                   ",
      "icbi                    ",
      "call_save_volatile      ",
      "mir_start               ",
      "mir_lowtableswitch      ",
      "ppc_data_int            ",
      "ppc_data_label          ",
      "ppc_add                 ",
      "ppc_add.                ",
      "ppc_addc                ",
      "ppc_adde                ",
      "ppc_addze               ",
      "ppc_addme               ",
      "ppc_addic               ",
      "ppc_addic.              ",
      "ppc_subf                ",
      "ppc_subf.               ",
      "ppc_subfc               ",
      "ppc_subfc.              ",
      "ppc_subfic              ",
      "ppc_subfe               ",
      "ppc_subfze              ",
      "ppc_subfme              ",
      "ppc_and                 ",
      "ppc_and.                ",
      "ppc_andi.               ",
      "ppc_andis.              ",
      "ppc_nand                ",
      "ppc_nand.               ",
      "ppc_andc                ",
      "ppc_andc.               ",
      "ppc_or                  ",
      "ppc_or.                 ",
      "ppc_move                ",
      "ppc_ori                 ",
      "ppc_oris                ",
      "ppc_nor                 ",
      "ppc_nor.                ",
      "ppc_orc                 ",
      "ppc_orc.                ",
      "ppc_xor                 ",
      "ppc_xor.                ",
      "ppc_xori                ",
      "ppc_xoris               ",
      "ppc_eqv                 ",
      "ppc_eqv.                ",
      "ppc_neg                 ",
      "ppc_neg.                ",
      "ppc_cntlzw              ",
      "ppc_extsb               ",
      "ppc_extsb.              ",
      "ppc_extsh               ",
      "ppc_extsh.              ",
      "ppc_slw                 ",
      "ppc_slw.                ",
      "ppc_slwi                ",
      "ppc_slwi.               ",
      "ppc_srw                 ",
      "ppc_srw.                ",
      "ppc_srwi                ",
      "ppc_srwi.               ",
      "ppc_sraw                ",
      "ppc_sraw.               ",
      "ppc_srawi               ",
      "ppc_srawi.              ",
      "ppc_rlwinm              ",
      "ppc_rlwinm.             ",
      "ppc_rlwimi              ",
      "ppc_rlwimi.             ",
      "ppc_rlwnm               ",
      "ppc_rlwnm.              ",
      "ppc_b                   ",
      "ppc_bl                  ",
      "ppc_bl_sys              ",
      "ppc_blr                 ",
      "ppc_bctr                ",
      "ppc_bctrl               ",
      "ppc_bctrl_sys           ",
      "ppc_bclr                ",
      "ppc_blrl                ",
      "ppc_bclrl               ",
      "ppc_bc                  ",
      "ppc_bcl                 ",
      "ppc_bcond               ",
      "ppc_bcond2              ",
      "ppc_bcctr               ",
      "ppc_bcc                 ",
      "ppc_addi                ",
      "ppc_addis               ",
      "ppc_ldi                 ",
      "ppc_ldis                ",
      "ppc_cmp                 ",
      "ppc_cmpi                ",
      "ppc_cmpl                ",
      "ppc_cmpli               ",
      "ppc_crand               ",
      "ppc_crandc              ",
      "ppc_cror                ",
      "ppc_crorc               ",
      "ppc_fmr                 ",
      "ppc_frsp                ",
      "ppc_fctiw               ",
      "ppc_fctiwz              ",
      "ppc_fadd                ",
      "ppc_fadds               ",
      "ppc_fsqrt               ",
      "ppc_fsqrts              ",
      "ppc_fabs                ",
      "ppc_fcmpo               ",
      "ppc_fcmpu               ",
      "ppc_fdiv                ",
      "ppc_fdivs               ",
      "ppc_divw                ",
      "ppc_divwu               ",
      "ppc_fmul                ",
      "ppc_fmuls               ",
      "ppc_fsel                ",
      "ppc_fmadd               ",
      "ppc_fmadds              ",
      "ppc_fmsub               ",
      "ppc_fmsubs              ",
      "ppc_fnmadd              ",
      "ppc_fnmadds             ",
      "ppc_fnmsub              ",
      "ppc_fnmsubs             ",
      "ppc_mulli               ",
      "ppc_mullw               ",
      "ppc_mulhw               ",
      "ppc_mulhwu              ",
      "ppc_fneg                ",
      "ppc_fsub                ",
      "ppc_fsubs               ",
      "ppc_lwz                 ",
      "ppc_lwzu                ",
      "ppc_lwzux               ",
      "ppc_lwzx                ",
      "ppc_lwarx               ",
      "ppc_lbz                 ",
      "ppc_lbzux               ",
      "ppc_lbzx                ",
      "ppc_lha                 ",
      "ppc_lhax                ",
      "ppc_lhz                 ",
      "ppc_lhzx                ",
      "ppc_lfd                 ",
      "ppc_lfdx                ",
      "ppc_lfs                 ",
      "ppc_lfsx                ",
      "ppc_lmw                 ",
      "ppc_stw                 ",
      "ppc_stwx                ",
      "ppc_stwcx.              ",
      "ppc_stwu                ",
      "ppc_stb                 ",
      "ppc_stbx                ",
      "ppc_sth                 ",
      "ppc_sthx                ",
      "ppc_stfd                ",
      "ppc_stfdx               ",
      "ppc_stfdu               ",
      "ppc_stfs                ",
      "ppc_stfsx               ",
      "ppc_stfsu               ",
      "ppc_stmw                ",
      "ppc_tw                  ",
      "ppc_twi                 ",
      "ppc_mfspr               ",
      "ppc_mtspr               ",
      "ppc_mftb                ",
      "ppc_mftbu               ",
      "ppc_hwsync              ",
      "ppc_sync                ",
      "ppc_isync               ",
      "ppc_dcbf                ",
      "ppc_dcbst               ",
      "ppc_dcbt                ",
      "ppc_dcbtst              ",
      "ppc_dcbz                ",
      "ppc_dcbzl               ",
      "ppc_icbi                ",
      "ppc64_extsw             ",
      "ppc64_extsw.            ",
      "ppc64_extzw             ",
      "ppc64_rldicl            ",
      "ppc64_rldicr            ",
      "ppc64_sld               ",
      "ppc64_sld.              ",
      "ppc64_sldi              ",
      "ppc64_srd               ",
      "ppc64_srd.              ",
      "ppc64_srad              ",
      "ppc64_srad.             ",
      "ppc64_sradi             ",
      "ppc64_sradi.            ",
      "ppc64_srdi              ",
      "ppc64_rldimi            ",
      "ppc64_rldimi.           ",
      "ppc64_cmp               ",
      "ppc64_cmpi              ",
      "ppc64_cmpl              ",
      "ppc64_cmpli             ",
      "ppc64_fcfid             ",
      "ppc64_fctidz            ",
      "ppc64_divd              ",
      "ppc64_mulld             ",
      "ppc64_ld                ",
      "ppc64_ldx               ",
      "ppc64_std               ",
      "ppc64_stdx              ",
      "ppc64_td                ",
      "ppc64_tdi               ",
      "ppc_cntlzadd.           ",
      "ppc_sraadd.i            ",
      "ppc_sradd.i             ",
      "ppc64_lwa               ",
      "ppc_lint                ",
      "ppc64_lwax              ",
      "ppc_lintx               ",
      "ppc_lintux              ",
      "ppc_ladd.               ",
      "ppc_ladd.x              ",
      "ppc_ladd.u              ",
      "ppc_ladd.ux             ",
      "ppc_ladd.arx            ",
      "ppc_stadd.              ",
      "ppc_stadd.x             ",
      "ppc_stadd.u             ",
      "ppc_stadd.ux            ",
      "ppc_stadd.cx.           ",
      "ppc_tadd.               ",
      "ppc_illegal_instruction ",
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
