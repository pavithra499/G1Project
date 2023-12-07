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
package org.jikesrvm.compilers.opt.lir2mir.ia32_32;

import static org.jikesrvm.compilers.opt.ir.Operators.*;
import static org.jikesrvm.compilers.opt.ir.ia32.ArchOperators.*;
import static org.jikesrvm.compilers.opt.lir2mir.ia32_32.BURS_Definitions.*;
import static org.jikesrvm.compilers.opt.ir.IRTools.*;

import org.jikesrvm.*;
import org.jikesrvm.classloader.*;
import org.jikesrvm.compilers.opt.ir.*;
import org.jikesrvm.compilers.opt.ir.ia32.*;
import org.jikesrvm.compilers.opt.ir.operand.*;
import org.jikesrvm.compilers.opt.ir.operand.ia32.*;
import org.jikesrvm.compilers.opt.lir2mir.ia32.BURS_Helpers;
import org.jikesrvm.compilers.opt.lir2mir.ia32_32.BURS_TreeNode;
import org.jikesrvm.compilers.opt.lir2mir.AbstractBURS_TreeNode;
import org.jikesrvm.compilers.opt.lir2mir.BURS;
import org.jikesrvm.compilers.opt.lir2mir.BURS_StateCoder;
import org.jikesrvm.compilers.opt.OptimizingCompilerException;
import org.jikesrvm.runtime.ArchEntrypoints;
import org.jikesrvm.util.Bits; //NOPMD

import org.vmmagic.unboxed.*;
import org.vmmagic.pragma.Inline;
import org.vmmagic.pragma.Pure;

/**
 * Machine-specific instruction selection rules.  Program generated.
 *
 * Note: some of the functions have been taken and modified
 * from the file gen.c, from the LCC compiler.
 * See $RVM_ROOT/rvm/src-generated/opt-burs/jburg/COPYRIGHT file for copyright restrictions.
 *
 * @see BURS
 *
 * NOTE: Program generated file, do not edit!
 */
@SuppressWarnings("unused") // Machine generated code is hard to get perfect
public class BURS_STATE extends BURS_Helpers implements BURS_StateCoder {

   public BURS_STATE(BURS b) {
      super(b);
   }

/*****************************************************************/
/*                                                               */
/*  BURS TEMPLATE                                                */
/*                                                               */
/*****************************************************************/

   /**
    * Gets the state of a BURS node. This accessor is used by BURS.
    *
    * @param a the node
    *
    * @return the node's state
    */
   private static AbstractBURS_TreeNode STATE(AbstractBURS_TreeNode a) { return a; }

   /***********************************************************************
    *
    *   This file contains BURG utilities
    *
    *   Note: some of the functions have been taken and modified
    *    from the file gen.c, from the LCC compiler.
    *
    ************************************************************************/
   
   /**
    * Prints a debug message. No-op if debugging is disabled.
    *
    * @param p the BURS node
    * @param rule the rule
    * @param cost the rule's cost
    * @param bestcost the best cost seen so far
    */
   private static void trace(AbstractBURS_TreeNode p, int rule, int cost, int bestcost) {
     if (BURS.DEBUG) {
       VM.sysWriteln(p + " matched " + BURS_Debug.string[rule] + " with cost " +
                     cost + " vs. " + bestcost);
     }
   }

   /**
    * Dumps the whole tree starting at the given node. No-op if
    * debugging is disabled.
    *
    * @param p the node to start at
    */
   public static void dumpTree(AbstractBURS_TreeNode p) {
     if (BURS.DEBUG) {
       VM.sysWrite(dumpTree("\n",p,1));
     }
   }

   public static String dumpTree(String out, AbstractBURS_TreeNode p, int indent) {
     if (p == null) return out;
     StringBuilder result = new StringBuilder(out);
     for (int i=0; i<indent; i++)
       result.append("   ");
     result.append(p);
     result.append('\n');
     if (p.getChild1() != null) {
       indent++;
       result.append(dumpTree("",p.getChild1(),indent));
       if (p.getChild2() != null) {
         result.append(dumpTree("",p.getChild2(),indent));
       }
     }
     return result.toString();
   }

   /**
    * Dumps the cover of a tree, i.e. the rules
    * that cover the tree with a minimal cost. No-op if debugging is
    * disabled.
    *
    * @param p the tree's root
    * @param goalnt the non-terminal that is a goal. This is an external rule number
    * @param indent number of spaces to use for indentation
    */
   public static void dumpCover(AbstractBURS_TreeNode p, byte goalnt, int indent){
      if (BURS.DEBUG) {
      if (p == null) return;
      int rule = STATE(p).rule(goalnt);
      VM.sysWrite(STATE(p).getCost(goalnt)+"\t");
      for (int i = 0; i < indent; i++)
        VM.sysWrite(' ');
      VM.sysWrite(BURS_Debug.string[rule]+"\n");
      for (int i = 0; i < nts[rule].length; i++)
        dumpCover(kids(p,rule,i), nts[rule][i], indent + 1);
      }
   }

   // caution: MARK should be used in single threaded mode,
   @Inline
   public static void mark(AbstractBURS_TreeNode p, byte goalnt) {
     if (p == null) return;
     int rule = STATE(p).rule(goalnt);
     byte act = action(rule);
     if ((act & EMIT_INSTRUCTION) != 0) {
       p.setNonTerminal(goalnt);
     }
     if (rule == 0) {
       if (BURS.DEBUG) {
         VM.sysWrite("marking " + p + " with a goalnt of " + goalnt + " failed as the rule " + rule + " has no action");
       }
       throw new OptimizingCompilerException("BURS", "rule missing in ",
         p.getInstructionString(), dumpTree("", p, 1));
     }
     mark_kids(p,rule);
   }
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
//ir.brg

  /**
   * Generate from ir.template and assembled rules files.
   */
  /** Sorted rule number to unsorted rule number map */
  private static int[] unsortedErnMap = {
    0, /* 0 - no rule */
    1, /* 1 - stm: r */
    3, /* 2 - r: czr */
    4, /* 3 - cz: czr */
    5, /* 4 - r: szpr */
    6, /* 5 - szp: szpr */
    7, /* 6 - riv: r */
    9, /* 7 - rlv: r */
    12, /* 8 - any: riv */
    85, /* 9 - address: address1scaledreg */
    97, /* 10 - address1scaledreg: address1reg */
    352, /* 11 - load8: sload8 */
    353, /* 12 - load8: uload8 */
    362, /* 13 - load16: sload16 */
    363, /* 14 - load16: uload16 */
    366, /* 15 - load16_32: load16 */
    367, /* 16 - load16_32: load32 */
    368, /* 17 - load8_16_32: load16_32 */
    369, /* 18 - load8_16_32: load8 */
    2, /* 19 - r: REGISTER */
    8, /* 20 - riv: INT_CONSTANT */
    10, /* 21 - rlv: LONG_CONSTANT */
    11, /* 22 - any: NULL */
    13, /* 23 - any: ADDRESS_CONSTANT */
    14, /* 24 - any: LONG_CONSTANT */
    16, /* 25 - stm: IG_PATCH_POINT */
    17, /* 26 - stm: UNINT_BEGIN */
    18, /* 27 - stm: UNINT_END */
    19, /* 28 - stm: YIELDPOINT_PROLOGUE */
    20, /* 29 - stm: YIELDPOINT_EPILOGUE */
    21, /* 30 - stm: YIELDPOINT_BACKEDGE */
    22, /* 31 - r: FRAMESIZE */
    24, /* 32 - stm: RESOLVE */
    25, /* 33 - stm: NOP */
    26, /* 34 - r: GUARD_MOVE */
    27, /* 35 - r: GUARD_COMBINE */
    29, /* 36 - stm: IR_PROLOGUE */
    30, /* 37 - r: GET_CAUGHT_EXCEPTION */
    32, /* 38 - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT) */
    33, /* 39 - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT) */
    34, /* 40 - stm: TRAP */
    64, /* 41 - stm: GOTO */
    66, /* 42 - stm: WRITE_FLOOR */
    67, /* 43 - stm: READ_CEILING */
    68, /* 44 - stm: FENCE */
    69, /* 45 - stm: PAUSE */
    70, /* 46 - stm: ILLEGAL_INSTRUCTION */
    71, /* 47 - stm: RETURN(NULL) */
    72, /* 48 - stm: RETURN(INT_CONSTANT) */
    74, /* 49 - stm: RETURN(LONG_CONSTANT) */
    83, /* 50 - r: GET_TIME_BASE */
    401, /* 51 - r: LONG_MOVE(LONG_CONSTANT) */
    531, /* 52 - stm: CLEAR_FLOATING_POINT_STATE */
    15, /* 53 - any: OTHER_OPERAND(any,any) */
    37, /* 54 - stm: TRAP_IF(r,r) */
    38, /* 55 - stm: TRAP_IF(load32,riv) */
    39, /* 56 - stm: TRAP_IF(riv,load32) */
    63, /* 57 - r: LONG_CMP(rlv,rlv) */
    75, /* 58 - r: CALL(r,any) */
    80, /* 59 - r: SYSCALL(r,any) */
    84, /* 60 - stm: YIELDPOINT_OSR(any,any) */
    87, /* 61 - address: INT_ADD(r,r) */
    88, /* 62 - address: INT_ADD(r,address1scaledreg) */
    89, /* 63 - address: INT_ADD(address1scaledreg,r) */
    91, /* 64 - address: INT_ADD(address1scaledreg,address1reg) */
    92, /* 65 - address: INT_ADD(address1reg,address1scaledreg) */
    137, /* 66 - r: BOOLEAN_CMP_INT(r,riv) */
    138, /* 67 - boolcmp: BOOLEAN_CMP_INT(r,riv) */
    155, /* 68 - r: BOOLEAN_CMP_INT(load32,riv) */
    156, /* 69 - boolcmp: BOOLEAN_CMP_INT(load32,riv) */
    157, /* 70 - r: BOOLEAN_CMP_INT(r,load32) */
    158, /* 71 - boolcmp: BOOLEAN_CMP_INT(riv,load32) */
    161, /* 72 - r: BOOLEAN_CMP_LONG(rlv,rlv) */
    162, /* 73 - boolcmp: BOOLEAN_CMP_LONG(rlv,rlv) */
    207, /* 74 - czr: INT_ADD(r,riv) */
    208, /* 75 - r: INT_ADD(r,riv) */
    209, /* 76 - czr: INT_ADD(r,load32) */
    210, /* 77 - czr: INT_ADD(load32,riv) */
    215, /* 78 - szpr: INT_AND(r,riv) */
    216, /* 79 - szp: INT_AND(r,riv) */
    217, /* 80 - szpr: INT_AND(r,load32) */
    218, /* 81 - szpr: INT_AND(load32,riv) */
    219, /* 82 - szp: INT_AND(load8_16_32,riv) */
    220, /* 83 - szp: INT_AND(r,load8_16_32) */
    225, /* 84 - r: INT_DIV(riv,riv) */
    226, /* 85 - r: INT_DIV(riv,load32) */
    227, /* 86 - r: UNSIGNED_DIV_64_32(rlv,riv) */
    228, /* 87 - r: UNSIGNED_DIV_64_32(rlv,load32) */
    229, /* 88 - stm: INT_IFCMP(r,riv) */
    232, /* 89 - stm: INT_IFCMP(uload8,r) */
    233, /* 90 - stm: INT_IFCMP(r,uload8) */
    235, /* 91 - stm: INT_IFCMP(load32,riv) */
    236, /* 92 - stm: INT_IFCMP(r,load32) */
    242, /* 93 - stm: INT_IFCMP2(r,riv) */
    243, /* 94 - stm: INT_IFCMP2(load32,riv) */
    244, /* 95 - stm: INT_IFCMP2(riv,load32) */
    245, /* 96 - r: INT_LOAD(riv,riv) */
    246, /* 97 - r: INT_LOAD(riv,address1scaledreg) */
    247, /* 98 - r: INT_LOAD(address1scaledreg,riv) */
    248, /* 99 - r: INT_LOAD(address1scaledreg,address1reg) */
    249, /* 100 - r: INT_LOAD(address1reg,address1scaledreg) */
    251, /* 101 - r: INT_ALOAD(riv,riv) */
    264, /* 102 - r: INT_MUL(r,riv) */
    265, /* 103 - r: INT_MUL(r,load32) */
    266, /* 104 - r: INT_MUL(load32,riv) */
    273, /* 105 - szpr: INT_OR(r,riv) */
    274, /* 106 - szpr: INT_OR(r,load32) */
    275, /* 107 - szpr: INT_OR(load32,riv) */
    280, /* 108 - r: INT_REM(riv,riv) */
    281, /* 109 - r: INT_REM(riv,load32) */
    282, /* 110 - r: UNSIGNED_REM_64_32(rlv,riv) */
    283, /* 111 - r: UNSIGNED_REM_64_32(rlv,load32) */
    293, /* 112 - szpr: INT_SHL(riv,riv) */
    302, /* 113 - szpr: INT_SHR(riv,riv) */
    314, /* 114 - czr: INT_SUB(riv,r) */
    315, /* 115 - r: INT_SUB(riv,r) */
    316, /* 116 - r: INT_SUB(load32,r) */
    317, /* 117 - czr: INT_SUB(riv,load32) */
    318, /* 118 - czr: INT_SUB(load32,riv) */
    324, /* 119 - szpr: INT_USHR(riv,riv) */
    330, /* 120 - szpr: INT_XOR(r,riv) */
    331, /* 121 - szpr: INT_XOR(r,load32) */
    332, /* 122 - szpr: INT_XOR(load32,riv) */
    338, /* 123 - r: INT_ADD(address1scaledreg,r) */
    339, /* 124 - r: INT_ADD(r,address1scaledreg) */
    340, /* 125 - r: INT_ADD(address1scaledreg,address1reg) */
    341, /* 126 - r: INT_ADD(address1reg,address1scaledreg) */
    344, /* 127 - r: BYTE_LOAD(riv,riv) */
    345, /* 128 - sload8: BYTE_LOAD(riv,riv) */
    346, /* 129 - r: BYTE_ALOAD(riv,riv) */
    347, /* 130 - sload8: BYTE_ALOAD(riv,riv) */
    348, /* 131 - r: UBYTE_LOAD(riv,riv) */
    349, /* 132 - uload8: UBYTE_LOAD(riv,riv) */
    350, /* 133 - r: UBYTE_ALOAD(riv,riv) */
    351, /* 134 - uload8: UBYTE_ALOAD(riv,riv) */
    354, /* 135 - r: SHORT_LOAD(riv,riv) */
    355, /* 136 - sload16: SHORT_LOAD(riv,riv) */
    356, /* 137 - r: SHORT_ALOAD(riv,riv) */
    357, /* 138 - sload16: SHORT_ALOAD(riv,riv) */
    358, /* 139 - r: USHORT_LOAD(riv,riv) */
    359, /* 140 - uload16: USHORT_LOAD(riv,riv) */
    360, /* 141 - r: USHORT_ALOAD(riv,riv) */
    361, /* 142 - uload16: USHORT_ALOAD(riv,riv) */
    364, /* 143 - load32: INT_LOAD(riv,riv) */
    365, /* 144 - load32: INT_ALOAD(riv,riv) */
    370, /* 145 - load64: LONG_LOAD(riv,riv) */
    371, /* 146 - load64: LONG_ALOAD(riv,riv) */
    383, /* 147 - r: LONG_ADD(r,rlv) */
    384, /* 148 - r: LONG_ADD(r,load64) */
    385, /* 149 - r: LONG_ADD(load64,rlv) */
    390, /* 150 - r: LONG_AND(r,rlv) */
    391, /* 151 - r: LONG_AND(r,load64) */
    392, /* 152 - r: LONG_AND(load64,rlv) */
    397, /* 153 - stm: LONG_IFCMP(r,rlv) */
    398, /* 154 - r: LONG_LOAD(riv,riv) */
    399, /* 155 - r: LONG_ALOAD(riv,riv) */
    403, /* 156 - r: LONG_MUL(r,rlv) */
    413, /* 157 - r: LONG_OR(r,rlv) */
    414, /* 158 - r: LONG_OR(r,load64) */
    415, /* 159 - r: LONG_OR(load64,rlv) */
    420, /* 160 - r: LONG_SHL(rlv,riv) */
    422, /* 161 - r: LONG_SHR(rlv,riv) */
    426, /* 162 - r: LONG_SUB(rlv,rlv) */
    427, /* 163 - r: LONG_SUB(rlv,load64) */
    428, /* 164 - r: LONG_SUB(load64,rlv) */
    431, /* 165 - r: LONG_USHR(rlv,riv) */
    433, /* 166 - r: LONG_XOR(r,rlv) */
    434, /* 167 - r: LONG_XOR(r,load64) */
    435, /* 168 - r: LONG_XOR(load64,rlv) */
    440, /* 169 - r: FLOAT_ADD(r,r) */
    441, /* 170 - r: FLOAT_ADD(r,float_load) */
    442, /* 171 - r: FLOAT_ADD(float_load,r) */
    443, /* 172 - r: DOUBLE_ADD(r,r) */
    444, /* 173 - r: DOUBLE_ADD(r,double_load) */
    445, /* 174 - r: DOUBLE_ADD(double_load,r) */
    446, /* 175 - r: FLOAT_SUB(r,r) */
    447, /* 176 - r: FLOAT_SUB(r,float_load) */
    448, /* 177 - r: DOUBLE_SUB(r,r) */
    449, /* 178 - r: DOUBLE_SUB(r,double_load) */
    450, /* 179 - r: FLOAT_MUL(r,r) */
    451, /* 180 - r: FLOAT_MUL(r,float_load) */
    452, /* 181 - r: FLOAT_MUL(float_load,r) */
    453, /* 182 - r: DOUBLE_MUL(r,r) */
    454, /* 183 - r: DOUBLE_MUL(r,double_load) */
    455, /* 184 - r: DOUBLE_MUL(double_load,r) */
    456, /* 185 - r: FLOAT_DIV(r,r) */
    457, /* 186 - r: FLOAT_DIV(r,float_load) */
    458, /* 187 - r: DOUBLE_DIV(r,r) */
    459, /* 188 - r: DOUBLE_DIV(r,double_load) */
    464, /* 189 - r: FLOAT_REM(r,r) */
    465, /* 190 - r: DOUBLE_REM(r,r) */
    470, /* 191 - r: DOUBLE_LOAD(riv,riv) */
    471, /* 192 - r: DOUBLE_LOAD(riv,rlv) */
    472, /* 193 - r: DOUBLE_LOAD(rlv,rlv) */
    473, /* 194 - double_load: DOUBLE_LOAD(riv,riv) */
    474, /* 195 - r: DOUBLE_ALOAD(riv,riv) */
    475, /* 196 - r: DOUBLE_ALOAD(rlv,riv) */
    476, /* 197 - double_load: DOUBLE_LOAD(rlv,rlv) */
    477, /* 198 - r: DOUBLE_ALOAD(riv,r) */
    478, /* 199 - r: DOUBLE_ALOAD(rlv,rlv) */
    479, /* 200 - double_load: DOUBLE_ALOAD(rlv,riv) */
    480, /* 201 - double_load: DOUBLE_ALOAD(riv,riv) */
    481, /* 202 - r: FLOAT_LOAD(riv,riv) */
    482, /* 203 - r: FLOAT_LOAD(rlv,rlv) */
    483, /* 204 - float_load: FLOAT_LOAD(riv,riv) */
    484, /* 205 - float_load: FLOAT_ALOAD(rlv,riv) */
    485, /* 206 - r: FLOAT_ALOAD(riv,riv) */
    486, /* 207 - r: FLOAT_ALOAD(rlv,riv) */
    487, /* 208 - r: FLOAT_ALOAD(riv,r) */
    488, /* 209 - r: FLOAT_ALOAD(rlv,rlv) */
    489, /* 210 - float_load: FLOAT_ALOAD(riv,riv) */
    532, /* 211 - stm: FLOAT_IFCMP(r,r) */
    533, /* 212 - stm: FLOAT_IFCMP(r,float_load) */
    534, /* 213 - stm: FLOAT_IFCMP(float_load,r) */
    535, /* 214 - stm: DOUBLE_IFCMP(r,r) */
    536, /* 215 - stm: DOUBLE_IFCMP(r,double_load) */
    537, /* 216 - stm: DOUBLE_IFCMP(double_load,r) */
    23, /* 217 - stm: LOWTABLESWITCH(r) */
    28, /* 218 - stm: NULL_CHECK(riv) */
    31, /* 219 - stm: SET_CAUGHT_EXCEPTION(r) */
    35, /* 220 - stm: TRAP_IF(r,INT_CONSTANT) */
    36, /* 221 - stm: TRAP_IF(r,LONG_CONSTANT) */
    40, /* 222 - uload8: INT_AND(load8_16_32,INT_CONSTANT) */
    41, /* 223 - r: INT_AND(load8_16_32,INT_CONSTANT) */
    42, /* 224 - r: INT_2BYTE(load8_16_32) */
    44, /* 225 - r: INT_AND(load16_32,INT_CONSTANT) */
    65, /* 226 - stm: PREFETCH(r) */
    73, /* 227 - stm: RETURN(r) */
    86, /* 228 - address: INT_MOVE(address) */
    90, /* 229 - address: INT_ADD(address1scaledreg,INT_CONSTANT) */
    93, /* 230 - address1reg: INT_ADD(r,INT_CONSTANT) */
    94, /* 231 - address1reg: INT_MOVE(r) */
    95, /* 232 - address1reg: INT_MOVE(address1reg) */
    96, /* 233 - address1reg: INT_ADD(address1reg,INT_CONSTANT) */
    98, /* 234 - address1scaledreg: INT_MOVE(address1scaledreg) */
    99, /* 235 - address1scaledreg: INT_SHL(r,INT_CONSTANT) */
    100, /* 236 - address1scaledreg: INT_ADD(address1scaledreg,INT_CONSTANT) */
    101, /* 237 - r: ADDR_2LONG(r) */
    102, /* 238 - r: ADDR_2LONG(load32) */
    139, /* 239 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    140, /* 240 - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    141, /* 241 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    142, /* 242 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) */
    143, /* 243 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    144, /* 244 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) */
    145, /* 245 - r: BOOLEAN_CMP_INT(cz,INT_CONSTANT) */
    146, /* 246 - boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT) */
    147, /* 247 - r: BOOLEAN_CMP_INT(szp,INT_CONSTANT) */
    148, /* 248 - boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT) */
    149, /* 249 - r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) */
    150, /* 250 - boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) */
    151, /* 251 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    152, /* 252 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    153, /* 253 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    154, /* 254 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    163, /* 255 - r: BOOLEAN_NOT(r) */
    172, /* 256 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    173, /* 257 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    174, /* 258 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    175, /* 259 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    187, /* 260 - r: INT_2BYTE(r) */
    188, /* 261 - r: INT_2BYTE(load8_16_32) */
    191, /* 262 - r: INT_2LONG(r) */
    192, /* 263 - r: INT_2LONG(load32) */
    197, /* 264 - r: INT_2SHORT(r) */
    198, /* 265 - r: INT_2SHORT(load16_32) */
    199, /* 266 - sload16: INT_2SHORT(load16_32) */
    202, /* 267 - szpr: INT_2USHORT(r) */
    203, /* 268 - uload16: INT_2USHORT(load16_32) */
    204, /* 269 - r: INT_2USHORT(load16_32) */
    230, /* 270 - stm: INT_IFCMP(r,INT_CONSTANT) */
    231, /* 271 - stm: INT_IFCMP(load8,INT_CONSTANT) */
    234, /* 272 - stm: INT_IFCMP(sload16,INT_CONSTANT) */
    237, /* 273 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) */
    238, /* 274 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) */
    239, /* 275 - stm: INT_IFCMP(cz,INT_CONSTANT) */
    240, /* 276 - stm: INT_IFCMP(szp,INT_CONSTANT) */
    241, /* 277 - stm: INT_IFCMP(bittest,INT_CONSTANT) */
    250, /* 278 - r: INT_LOAD(address,INT_CONSTANT) */
    252, /* 279 - r: INT_MOVE(riv) */
    253, /* 280 - czr: INT_MOVE(czr) */
    254, /* 281 - cz: INT_MOVE(cz) */
    255, /* 282 - szpr: INT_MOVE(szpr) */
    256, /* 283 - szp: INT_MOVE(szp) */
    257, /* 284 - sload8: INT_MOVE(sload8) */
    258, /* 285 - uload8: INT_MOVE(uload8) */
    259, /* 286 - load8: INT_MOVE(load8) */
    260, /* 287 - sload16: INT_MOVE(sload16) */
    261, /* 288 - uload16: INT_MOVE(uload16) */
    262, /* 289 - load16: INT_MOVE(load16) */
    263, /* 290 - load32: INT_MOVE(load32) */
    267, /* 291 - szpr: INT_NEG(r) */
    270, /* 292 - r: INT_NOT(r) */
    294, /* 293 - szpr: INT_SHL(r,INT_CONSTANT) */
    295, /* 294 - r: INT_SHL(r,INT_CONSTANT) */
    303, /* 295 - szpr: INT_SHR(riv,INT_CONSTANT) */
    325, /* 296 - szpr: INT_USHR(riv,INT_CONSTANT) */
    342, /* 297 - r: INT_ADD(address,INT_CONSTANT) */
    343, /* 298 - r: INT_MOVE(address) */
    372, /* 299 - r: LONG_2INT(r) */
    375, /* 300 - r: LONG_2INT(load64) */
    376, /* 301 - load32: LONG_2INT(load64) */
    400, /* 302 - r: LONG_MOVE(r) */
    402, /* 303 - load64: LONG_MOVE(load64) */
    407, /* 304 - r: LONG_NEG(r) */
    410, /* 305 - r: LONG_NOT(r) */
    460, /* 306 - r: FLOAT_NEG(r) */
    461, /* 307 - r: DOUBLE_NEG(r) */
    462, /* 308 - r: FLOAT_SQRT(r) */
    463, /* 309 - r: DOUBLE_SQRT(r) */
    466, /* 310 - r: LONG_2FLOAT(r) */
    467, /* 311 - r: LONG_2DOUBLE(r) */
    468, /* 312 - r: FLOAT_MOVE(r) */
    469, /* 313 - r: DOUBLE_MOVE(r) */
    508, /* 314 - r: INT_2FLOAT(riv) */
    509, /* 315 - r: INT_2FLOAT(load32) */
    510, /* 316 - r: INT_2DOUBLE(riv) */
    511, /* 317 - r: INT_2DOUBLE(load32) */
    512, /* 318 - r: FLOAT_2DOUBLE(r) */
    513, /* 319 - r: FLOAT_2DOUBLE(float_load) */
    514, /* 320 - r: DOUBLE_2FLOAT(r) */
    515, /* 321 - r: DOUBLE_2FLOAT(double_load) */
    516, /* 322 - r: FLOAT_2INT(r) */
    517, /* 323 - r: FLOAT_2LONG(r) */
    518, /* 324 - r: DOUBLE_2INT(r) */
    519, /* 325 - r: DOUBLE_2LONG(r) */
    520, /* 326 - r: FLOAT_AS_INT_BITS(r) */
    521, /* 327 - load32: FLOAT_AS_INT_BITS(float_load) */
    522, /* 328 - r: DOUBLE_AS_LONG_BITS(r) */
    523, /* 329 - load64: DOUBLE_AS_LONG_BITS(double_load) */
    524, /* 330 - r: INT_BITS_AS_FLOAT(riv) */
    525, /* 331 - float_load: INT_BITS_AS_FLOAT(load32) */
    526, /* 332 - r: LONG_BITS_AS_DOUBLE(rlv) */
    527, /* 333 - double_load: LONG_BITS_AS_DOUBLE(load64) */
    528, /* 334 - r: MATERIALIZE_FP_CONSTANT(any) */
    529, /* 335 - float_load: MATERIALIZE_FP_CONSTANT(any) */
    530, /* 336 - double_load: MATERIALIZE_FP_CONSTANT(any) */
    43, /* 337 - r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT) */
    45, /* 338 - r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT) */
    129, /* 339 - bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT) */
    132, /* 340 - bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) */
    193, /* 341 - r: LONG_AND(INT_2LONG(r),LONG_CONSTANT) */
    194, /* 342 - r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT) */
    195, /* 343 - r: LONG_SHL(INT_2LONG(r),INT_CONSTANT) */
    196, /* 344 - r: LONG_SHL(INT_2LONG(load64),INT_CONSTANT) */
    296, /* 345 - szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) */
    377, /* 346 - r: LONG_2INT(LONG_USHR(r,INT_CONSTANT)) */
    378, /* 347 - r: LONG_2INT(LONG_SHR(r,INT_CONSTANT)) */
    379, /* 348 - r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) */
    380, /* 349 - r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) */
    381, /* 350 - load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) */
    382, /* 351 - load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) */
    405, /* 352 - r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_CONSTANT) */
    46, /* 353 - stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv)) */
    47, /* 354 - stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv)) */
    48, /* 355 - stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv)) */
    49, /* 356 - stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv)) */
    50, /* 357 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv)) */
    51, /* 358 - stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv)) */
    52, /* 359 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r)) */
    53, /* 360 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv)) */
    54, /* 361 - stm: INT_ASTORE(riv,OTHER_OPERAND(r,r)) */
    55, /* 362 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv)) */
    56, /* 363 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv)) */
    57, /* 364 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv)) */
    58, /* 365 - stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv)) */
    59, /* 366 - stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv)) */
    60, /* 367 - stm: LONG_ASTORE(r,OTHER_OPERAND(r,r)) */
    159, /* 368 - stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv)) */
    160, /* 369 - stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv)) */
    166, /* 370 - stm: BYTE_STORE(riv,OTHER_OPERAND(riv,riv)) */
    167, /* 371 - stm: BYTE_STORE(load8,OTHER_OPERAND(riv,riv)) */
    168, /* 372 - stm: BYTE_ASTORE(riv,OTHER_OPERAND(riv,riv)) */
    169, /* 373 - stm: BYTE_ASTORE(load8,OTHER_OPERAND(riv,riv)) */
    170, /* 374 - r: CMP_CMOV(r,OTHER_OPERAND(riv,any)) */
    177, /* 375 - r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any)) */
    178, /* 376 - r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any)) */
    180, /* 377 - r: CMP_CMOV(load32,OTHER_OPERAND(riv,any)) */
    181, /* 378 - r: CMP_CMOV(riv,OTHER_OPERAND(load32,any)) */
    308, /* 379 - stm: INT_STORE(riv,OTHER_OPERAND(riv,riv)) */
    309, /* 380 - stm: INT_STORE(riv,OTHER_OPERAND(riv,address1scaledreg)) */
    310, /* 381 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,riv)) */
    311, /* 382 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg)) */
    312, /* 383 - stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg)) */
    337, /* 384 - r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any)) */
    424, /* 385 - stm: LONG_STORE(r,OTHER_OPERAND(riv,riv)) */
    490, /* 386 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv)) */
    491, /* 387 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv)) */
    492, /* 388 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv)) */
    493, /* 389 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv)) */
    494, /* 390 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv)) */
    495, /* 391 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv)) */
    496, /* 392 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv)) */
    497, /* 393 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv)) */
    498, /* 394 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r)) */
    499, /* 395 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv)) */
    500, /* 396 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv)) */
    501, /* 397 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv)) */
    502, /* 398 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv)) */
    503, /* 399 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv)) */
    504, /* 400 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv)) */
    505, /* 401 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv)) */
    506, /* 402 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv)) */
    507, /* 403 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r)) */
    538, /* 404 - r: FCMP_CMOV(r,OTHER_OPERAND(r,any)) */
    539, /* 405 - r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any)) */
    540, /* 406 - r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any)) */
    541, /* 407 - r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any)) */
    542, /* 408 - r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any)) */
    543, /* 409 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,any)) */
    548, /* 410 - r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any)) */
    549, /* 411 - r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any)) */
    566, /* 412 - stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv)) */
    567, /* 413 - stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv)) */
    568, /* 414 - stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv)) */
    569, /* 415 - stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv)) */
    61, /* 416 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv)) */
    62, /* 417 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv)) */
    425, /* 418 - stm: LONG_STORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv)) */
    76, /* 419 - r: CALL(BRANCH_TARGET,any) */
    78, /* 420 - r: CALL(INT_CONSTANT,any) */
    82, /* 421 - r: SYSCALL(INT_CONSTANT,any) */
    77, /* 422 - r: CALL(INT_LOAD(riv,riv),any) */
    79, /* 423 - r: CALL(LONG_LOAD(rlv,rlv),any) */
    81, /* 424 - r: SYSCALL(INT_LOAD(riv,riv),any) */
    103, /* 425 - r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))) */
    104, /* 426 - r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) */
    105, /* 427 - r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) */
    106, /* 428 - r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) */
    107, /* 429 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))) */
    108, /* 430 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))) */
    109, /* 431 - r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) */
    126, /* 432 - r: ATTEMPT_LONG(riv,OTHER_OPERAND(riv,OTHER_OPERAND(rlv,rlv))) */
    544, /* 433 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load))) */
    545, /* 434 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load))) */
    546, /* 435 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r))) */
    547, /* 436 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r))) */
    110, /* 437 - r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))) */
    111, /* 438 - r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))) */
    112, /* 439 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    113, /* 440 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    114, /* 441 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    115, /* 442 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    116, /* 443 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    119, /* 444 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    120, /* 445 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    121, /* 446 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    122, /* 447 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    123, /* 448 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    117, /* 449 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    124, /* 450 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    118, /* 451 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    125, /* 452 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    127, /* 453 - bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    128, /* 454 - bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    130, /* 455 - bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    131, /* 456 - bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    133, /* 457 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r) */
    134, /* 458 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32) */
    135, /* 459 - bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) */
    136, /* 460 - bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) */
    164, /* 461 - stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    165, /* 462 - stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    268, /* 463 - stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    269, /* 464 - stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    271, /* 465 - stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    272, /* 466 - stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    298, /* 467 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    300, /* 468 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    305, /* 469 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    307, /* 470 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    327, /* 471 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    329, /* 472 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    408, /* 473 - stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    409, /* 474 - stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    411, /* 475 - stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    412, /* 476 - stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    171, /* 477 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any)) */
    176, /* 478 - r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any)) */
    179, /* 479 - r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any)) */
    182, /* 480 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) */
    183, /* 481 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) */
    184, /* 482 - r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any)) */
    185, /* 483 - r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any)) */
    186, /* 484 - r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any)) */
    189, /* 485 - stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) */
    190, /* 486 - stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) */
    200, /* 487 - stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) */
    201, /* 488 - stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) */
    205, /* 489 - stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) */
    206, /* 490 - stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) */
    373, /* 491 - stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) */
    374, /* 492 - stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) */
    211, /* 493 - stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    213, /* 494 - stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    221, /* 495 - stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    223, /* 496 - stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    276, /* 497 - stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    278, /* 498 - stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    319, /* 499 - stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    321, /* 500 - stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    333, /* 501 - stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    335, /* 502 - stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    386, /* 503 - stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    388, /* 504 - stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    393, /* 505 - stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    395, /* 506 - stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    416, /* 507 - stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    418, /* 508 - stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    429, /* 509 - stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    430, /* 510 - stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    436, /* 511 - stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    438, /* 512 - stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    212, /* 513 - stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    214, /* 514 - stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    222, /* 515 - stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    224, /* 516 - stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    277, /* 517 - stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    279, /* 518 - stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    320, /* 519 - stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    322, /* 520 - stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    334, /* 521 - stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    336, /* 522 - stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    387, /* 523 - stm: LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    389, /* 524 - stm: LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    394, /* 525 - stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    396, /* 526 - stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    417, /* 527 - stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    419, /* 528 - stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    437, /* 529 - stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    439, /* 530 - stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    284, /* 531 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) */
    285, /* 532 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) */
    286, /* 533 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) */
    287, /* 534 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) */
    404, /* 535 - r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_AND(rlv,LONG_CONSTANT)) */
    406, /* 536 - r: LONG_MUL(INT_2LONG(riv),INT_2LONG(riv)) */
    288, /* 537 - r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT))) */
    291, /* 538 - r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT))) */
    289, /* 539 - r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT))) */
    290, /* 540 - r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT))) */
    292, /* 541 - szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT)) */
    301, /* 542 - szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT)) */
    313, /* 543 - stm: INT_STORE(riv,OTHER_OPERAND(address,INT_CONSTANT)) */
    323, /* 544 - szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT)) */
    421, /* 545 - r: LONG_SHL(rlv,INT_AND(riv,INT_CONSTANT)) */
    423, /* 546 - r: LONG_SHR(rlv,INT_AND(riv,INT_CONSTANT)) */
    432, /* 547 - r: LONG_USHR(rlv,INT_AND(riv,INT_CONSTANT)) */
    297, /* 548 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    299, /* 549 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    304, /* 550 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    306, /* 551 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    326, /* 552 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    328, /* 553 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    550, /* 554 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    551, /* 555 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    558, /* 556 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) */
    559, /* 557 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) */
    552, /* 558 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) */
    553, /* 559 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) */
    560, /* 560 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    561, /* 561 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    554, /* 562 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) */
    555, /* 563 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) */
    562, /* 564 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    563, /* 565 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    556, /* 566 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    557, /* 567 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    564, /* 568 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r)))) */
  };

  /** Ragged array for non-terminal leaves of r_NT,  */
  private static final byte[] nts_0 = { r_NT,  };
  /** Ragged array for non-terminal leaves of czr_NT,  */
  private static final byte[] nts_1 = { czr_NT,  };
  /** Ragged array for non-terminal leaves of szpr_NT,  */
  private static final byte[] nts_2 = { szpr_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT,  */
  private static final byte[] nts_3 = { riv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT,  */
  private static final byte[] nts_4 = { address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT,  */
  private static final byte[] nts_5 = { address1reg_NT,  };
  /** Ragged array for non-terminal leaves of sload8_NT,  */
  private static final byte[] nts_6 = { sload8_NT,  };
  /** Ragged array for non-terminal leaves of uload8_NT,  */
  private static final byte[] nts_7 = { uload8_NT,  };
  /** Ragged array for non-terminal leaves of sload16_NT,  */
  private static final byte[] nts_8 = { sload16_NT,  };
  /** Ragged array for non-terminal leaves of uload16_NT,  */
  private static final byte[] nts_9 = { uload16_NT,  };
  /** Ragged array for non-terminal leaves of load16_NT,  */
  private static final byte[] nts_10 = { load16_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT,  */
  private static final byte[] nts_11 = { load32_NT,  };
  /** Ragged array for non-terminal leaves of load16_32_NT,  */
  private static final byte[] nts_12 = { load16_32_NT,  };
  /** Ragged array for non-terminal leaves of load8_NT,  */
  private static final byte[] nts_13 = { load8_NT,  };
  /** Ragged array for non-terminal leaves of  */
  private static final byte[] nts_14 = {  };
  /** Ragged array for non-terminal leaves of any_NT, any_NT,  */
  private static final byte[] nts_15 = { any_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT,  */
  private static final byte[] nts_16 = { r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT, riv_NT,  */
  private static final byte[] nts_17 = { load32_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, load32_NT,  */
  private static final byte[] nts_18 = { riv_NT, load32_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT,  */
  private static final byte[] nts_19 = { rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, any_NT,  */
  private static final byte[] nts_20 = { r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, address1scaledreg_NT,  */
  private static final byte[] nts_21 = { r_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, r_NT,  */
  private static final byte[] nts_22 = { address1scaledreg_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, address1reg_NT,  */
  private static final byte[] nts_23 = { address1scaledreg_NT, address1reg_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT, address1scaledreg_NT,  */
  private static final byte[] nts_24 = { address1reg_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT,  */
  private static final byte[] nts_25 = { r_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load32_NT,  */
  private static final byte[] nts_26 = { r_NT, load32_NT,  };
  /** Ragged array for non-terminal leaves of load8_16_32_NT, riv_NT,  */
  private static final byte[] nts_27 = { load8_16_32_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load8_16_32_NT,  */
  private static final byte[] nts_28 = { r_NT, load8_16_32_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT,  */
  private static final byte[] nts_29 = { riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, riv_NT,  */
  private static final byte[] nts_30 = { rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, load32_NT,  */
  private static final byte[] nts_31 = { rlv_NT, load32_NT,  };
  /** Ragged array for non-terminal leaves of uload8_NT, r_NT,  */
  private static final byte[] nts_32 = { uload8_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, uload8_NT,  */
  private static final byte[] nts_33 = { r_NT, uload8_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1scaledreg_NT,  */
  private static final byte[] nts_34 = { riv_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, riv_NT,  */
  private static final byte[] nts_35 = { address1scaledreg_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, r_NT,  */
  private static final byte[] nts_36 = { riv_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT, r_NT,  */
  private static final byte[] nts_37 = { load32_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT,  */
  private static final byte[] nts_38 = { r_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load64_NT,  */
  private static final byte[] nts_39 = { r_NT, load64_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, rlv_NT,  */
  private static final byte[] nts_40 = { load64_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, load64_NT,  */
  private static final byte[] nts_41 = { rlv_NT, load64_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, float_load_NT,  */
  private static final byte[] nts_42 = { r_NT, float_load_NT,  };
  /** Ragged array for non-terminal leaves of float_load_NT, r_NT,  */
  private static final byte[] nts_43 = { float_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, double_load_NT,  */
  private static final byte[] nts_44 = { r_NT, double_load_NT,  };
  /** Ragged array for non-terminal leaves of double_load_NT, r_NT,  */
  private static final byte[] nts_45 = { double_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT,  */
  private static final byte[] nts_46 = { riv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of load8_16_32_NT,  */
  private static final byte[] nts_47 = { load8_16_32_NT,  };
  /** Ragged array for non-terminal leaves of address_NT,  */
  private static final byte[] nts_48 = { address_NT,  };
  /** Ragged array for non-terminal leaves of cz_NT,  */
  private static final byte[] nts_49 = { cz_NT,  };
  /** Ragged array for non-terminal leaves of szp_NT,  */
  private static final byte[] nts_50 = { szp_NT,  };
  /** Ragged array for non-terminal leaves of bittest_NT,  */
  private static final byte[] nts_51 = { bittest_NT,  };
  /** Ragged array for non-terminal leaves of boolcmp_NT,  */
  private static final byte[] nts_52 = { boolcmp_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT,  */
  private static final byte[] nts_53 = { load64_NT,  };
  /** Ragged array for non-terminal leaves of float_load_NT,  */
  private static final byte[] nts_54 = { float_load_NT,  };
  /** Ragged array for non-terminal leaves of double_load_NT,  */
  private static final byte[] nts_55 = { double_load_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT,  */
  private static final byte[] nts_56 = { rlv_NT,  };
  /** Ragged array for non-terminal leaves of any_NT,  */
  private static final byte[] nts_57 = { any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_58 = { riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load16_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_59 = { load16_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_60 = { rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_61 = { riv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, r_NT, r_NT,  */
  private static final byte[] nts_62 = { riv_NT, r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_63 = { riv_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, rlv_NT,  */
  private static final byte[] nts_64 = { riv_NT, riv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_65 = { r_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_66 = { r_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT,  */
  private static final byte[] nts_67 = { r_NT, r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of boolcmp_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_68 = { boolcmp_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load8_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_69 = { load8_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, any_NT,  */
  private static final byte[] nts_70 = { r_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of uload8_NT, riv_NT, any_NT,  */
  private static final byte[] nts_71 = { uload8_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, uload8_NT, any_NT,  */
  private static final byte[] nts_72 = { riv_NT, uload8_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT, riv_NT, any_NT,  */
  private static final byte[] nts_73 = { load32_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, load32_NT, any_NT,  */
  private static final byte[] nts_74 = { riv_NT, load32_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, address1scaledreg_NT,  */
  private static final byte[] nts_75 = { riv_NT, riv_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1scaledreg_NT, riv_NT,  */
  private static final byte[] nts_76 = { riv_NT, address1scaledreg_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1scaledreg_NT, address1reg_NT,  */
  private static final byte[] nts_77 = { riv_NT, address1scaledreg_NT, address1reg_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1reg_NT, address1scaledreg_NT,  */
  private static final byte[] nts_78 = { riv_NT, address1reg_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, any_NT,  */
  private static final byte[] nts_79 = { r_NT, rlv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, rlv_NT,  */
  private static final byte[] nts_80 = { r_NT, riv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_81 = { r_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, any_NT,  */
  private static final byte[] nts_82 = { r_NT, r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, float_load_NT, any_NT,  */
  private static final byte[] nts_83 = { r_NT, float_load_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, double_load_NT, any_NT,  */
  private static final byte[] nts_84 = { r_NT, double_load_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of float_load_NT, r_NT, any_NT,  */
  private static final byte[] nts_85 = { float_load_NT, r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of double_load_NT, r_NT, any_NT,  */
  private static final byte[] nts_86 = { double_load_NT, r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_87 = { load64_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_88 = { load64_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, any_NT,  */
  private static final byte[] nts_89 = { riv_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, any_NT,  */
  private static final byte[] nts_90 = { rlv_NT, rlv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_91 = { riv_NT, riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_92 = { riv_NT, rlv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_93 = { rlv_NT, rlv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, address1scaledreg_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_94 = { r_NT, address1scaledreg_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, r_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_95 = { address1scaledreg_NT, r_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, address1reg_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_96 = { address1scaledreg_NT, address1reg_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT, address1scaledreg_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_97 = { address1reg_NT, address1scaledreg_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_98 = { riv_NT, riv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT, float_load_NT,  */
  private static final byte[] nts_99 = { r_NT, r_NT, r_NT, float_load_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT, double_load_NT,  */
  private static final byte[] nts_100 = { r_NT, r_NT, r_NT, double_load_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, float_load_NT, r_NT,  */
  private static final byte[] nts_101 = { r_NT, r_NT, float_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, double_load_NT, r_NT,  */
  private static final byte[] nts_102 = { r_NT, r_NT, double_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of address_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_103 = { address_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load8_NT, any_NT,  */
  private static final byte[] nts_104 = { load8_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of sload16_NT, any_NT,  */
  private static final byte[] nts_105 = { sload16_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of boolcmp_NT, any_NT,  */
  private static final byte[] nts_106 = { boolcmp_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of bittest_NT, any_NT,  */
  private static final byte[] nts_107 = { bittest_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of cz_NT, any_NT,  */
  private static final byte[] nts_108 = { cz_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of szp_NT, any_NT,  */
  private static final byte[] nts_109 = { szp_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_110 = { riv_NT, riv_NT, riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_111 = { rlv_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_112 = { r_NT, riv_NT, riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_113 = { r_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT, r_NT,  */
  private static final byte[] nts_114 = { r_NT, r_NT, r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address_NT,  */
  private static final byte[] nts_115 = { riv_NT, address_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, r_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_116 = { riv_NT, riv_NT, r_NT, riv_NT, riv_NT,  };

  /** Map non-terminal to non-terminal leaves */
  private static final byte[][] nts = {
    null, /* 0 */
    nts_0,  // 1 - stm: r 
    nts_1,  // 2 - r: czr 
    nts_1,  // 3 - cz: czr 
    nts_2,  // 4 - r: szpr 
    nts_2,  // 5 - szp: szpr 
    nts_0,  // 6 - riv: r 
    nts_0,  // 7 - rlv: r 
    nts_3,  // 8 - any: riv 
    nts_4,  // 9 - address: address1scaledreg 
    nts_5,  // 10 - address1scaledreg: address1reg 
    nts_6,  // 11 - load8: sload8 
    nts_7,  // 12 - load8: uload8 
    nts_8,  // 13 - load16: sload16 
    nts_9,  // 14 - load16: uload16 
    nts_10, // 15 - load16_32: load16 
    nts_11, // 16 - load16_32: load32 
    nts_12, // 17 - load8_16_32: load16_32 
    nts_13, // 18 - load8_16_32: load8 
    nts_14, // 19 - r: REGISTER 
    nts_14, // 20 - riv: INT_CONSTANT 
    nts_14, // 21 - rlv: LONG_CONSTANT 
    nts_14, // 22 - any: NULL 
    nts_14, // 23 - any: ADDRESS_CONSTANT 
    nts_14, // 24 - any: LONG_CONSTANT 
    nts_14, // 25 - stm: IG_PATCH_POINT 
    nts_14, // 26 - stm: UNINT_BEGIN 
    nts_14, // 27 - stm: UNINT_END 
    nts_14, // 28 - stm: YIELDPOINT_PROLOGUE 
    nts_14, // 29 - stm: YIELDPOINT_EPILOGUE 
    nts_14, // 30 - stm: YIELDPOINT_BACKEDGE 
    nts_14, // 31 - r: FRAMESIZE 
    nts_14, // 32 - stm: RESOLVE 
    nts_14, // 33 - stm: NOP 
    nts_14, // 34 - r: GUARD_MOVE 
    nts_14, // 35 - r: GUARD_COMBINE 
    nts_14, // 36 - stm: IR_PROLOGUE 
    nts_14, // 37 - r: GET_CAUGHT_EXCEPTION 
    nts_14, // 38 - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT) 
    nts_14, // 39 - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT) 
    nts_14, // 40 - stm: TRAP 
    nts_14, // 41 - stm: GOTO 
    nts_14, // 42 - stm: WRITE_FLOOR 
    nts_14, // 43 - stm: READ_CEILING 
    nts_14, // 44 - stm: FENCE 
    nts_14, // 45 - stm: PAUSE 
    nts_14, // 46 - stm: ILLEGAL_INSTRUCTION 
    nts_14, // 47 - stm: RETURN(NULL) 
    nts_14, // 48 - stm: RETURN(INT_CONSTANT) 
    nts_14, // 49 - stm: RETURN(LONG_CONSTANT) 
    nts_14, // 50 - r: GET_TIME_BASE 
    nts_14, // 51 - r: LONG_MOVE(LONG_CONSTANT) 
    nts_14, // 52 - stm: CLEAR_FLOATING_POINT_STATE 
    nts_15, // 53 - any: OTHER_OPERAND(any,any) 
    nts_16, // 54 - stm: TRAP_IF(r,r) 
    nts_17, // 55 - stm: TRAP_IF(load32,riv) 
    nts_18, // 56 - stm: TRAP_IF(riv,load32) 
    nts_19, // 57 - r: LONG_CMP(rlv,rlv) 
    nts_20, // 58 - r: CALL(r,any) 
    nts_20, // 59 - r: SYSCALL(r,any) 
    nts_15, // 60 - stm: YIELDPOINT_OSR(any,any) 
    nts_16, // 61 - address: INT_ADD(r,r) 
    nts_21, // 62 - address: INT_ADD(r,address1scaledreg) 
    nts_22, // 63 - address: INT_ADD(address1scaledreg,r) 
    nts_23, // 64 - address: INT_ADD(address1scaledreg,address1reg) 
    nts_24, // 65 - address: INT_ADD(address1reg,address1scaledreg) 
    nts_25, // 66 - r: BOOLEAN_CMP_INT(r,riv) 
    nts_25, // 67 - boolcmp: BOOLEAN_CMP_INT(r,riv) 
    nts_17, // 68 - r: BOOLEAN_CMP_INT(load32,riv) 
    nts_17, // 69 - boolcmp: BOOLEAN_CMP_INT(load32,riv) 
    nts_26, // 70 - r: BOOLEAN_CMP_INT(r,load32) 
    nts_18, // 71 - boolcmp: BOOLEAN_CMP_INT(riv,load32) 
    nts_19, // 72 - r: BOOLEAN_CMP_LONG(rlv,rlv) 
    nts_19, // 73 - boolcmp: BOOLEAN_CMP_LONG(rlv,rlv) 
    nts_25, // 74 - czr: INT_ADD(r,riv) 
    nts_25, // 75 - r: INT_ADD(r,riv) 
    nts_26, // 76 - czr: INT_ADD(r,load32) 
    nts_17, // 77 - czr: INT_ADD(load32,riv) 
    nts_25, // 78 - szpr: INT_AND(r,riv) 
    nts_25, // 79 - szp: INT_AND(r,riv) 
    nts_26, // 80 - szpr: INT_AND(r,load32) 
    nts_17, // 81 - szpr: INT_AND(load32,riv) 
    nts_27, // 82 - szp: INT_AND(load8_16_32,riv) 
    nts_28, // 83 - szp: INT_AND(r,load8_16_32) 
    nts_29, // 84 - r: INT_DIV(riv,riv) 
    nts_18, // 85 - r: INT_DIV(riv,load32) 
    nts_30, // 86 - r: UNSIGNED_DIV_64_32(rlv,riv) 
    nts_31, // 87 - r: UNSIGNED_DIV_64_32(rlv,load32) 
    nts_25, // 88 - stm: INT_IFCMP(r,riv) 
    nts_32, // 89 - stm: INT_IFCMP(uload8,r) 
    nts_33, // 90 - stm: INT_IFCMP(r,uload8) 
    nts_17, // 91 - stm: INT_IFCMP(load32,riv) 
    nts_26, // 92 - stm: INT_IFCMP(r,load32) 
    nts_25, // 93 - stm: INT_IFCMP2(r,riv) 
    nts_17, // 94 - stm: INT_IFCMP2(load32,riv) 
    nts_18, // 95 - stm: INT_IFCMP2(riv,load32) 
    nts_29, // 96 - r: INT_LOAD(riv,riv) 
    nts_34, // 97 - r: INT_LOAD(riv,address1scaledreg) 
    nts_35, // 98 - r: INT_LOAD(address1scaledreg,riv) 
    nts_23, // 99 - r: INT_LOAD(address1scaledreg,address1reg) 
    nts_24, // 100 - r: INT_LOAD(address1reg,address1scaledreg) 
    nts_29, // 101 - r: INT_ALOAD(riv,riv) 
    nts_25, // 102 - r: INT_MUL(r,riv) 
    nts_26, // 103 - r: INT_MUL(r,load32) 
    nts_17, // 104 - r: INT_MUL(load32,riv) 
    nts_25, // 105 - szpr: INT_OR(r,riv) 
    nts_26, // 106 - szpr: INT_OR(r,load32) 
    nts_17, // 107 - szpr: INT_OR(load32,riv) 
    nts_29, // 108 - r: INT_REM(riv,riv) 
    nts_18, // 109 - r: INT_REM(riv,load32) 
    nts_30, // 110 - r: UNSIGNED_REM_64_32(rlv,riv) 
    nts_31, // 111 - r: UNSIGNED_REM_64_32(rlv,load32) 
    nts_29, // 112 - szpr: INT_SHL(riv,riv) 
    nts_29, // 113 - szpr: INT_SHR(riv,riv) 
    nts_36, // 114 - czr: INT_SUB(riv,r) 
    nts_36, // 115 - r: INT_SUB(riv,r) 
    nts_37, // 116 - r: INT_SUB(load32,r) 
    nts_18, // 117 - czr: INT_SUB(riv,load32) 
    nts_17, // 118 - czr: INT_SUB(load32,riv) 
    nts_29, // 119 - szpr: INT_USHR(riv,riv) 
    nts_25, // 120 - szpr: INT_XOR(r,riv) 
    nts_26, // 121 - szpr: INT_XOR(r,load32) 
    nts_17, // 122 - szpr: INT_XOR(load32,riv) 
    nts_22, // 123 - r: INT_ADD(address1scaledreg,r) 
    nts_21, // 124 - r: INT_ADD(r,address1scaledreg) 
    nts_23, // 125 - r: INT_ADD(address1scaledreg,address1reg) 
    nts_24, // 126 - r: INT_ADD(address1reg,address1scaledreg) 
    nts_29, // 127 - r: BYTE_LOAD(riv,riv) 
    nts_29, // 128 - sload8: BYTE_LOAD(riv,riv) 
    nts_29, // 129 - r: BYTE_ALOAD(riv,riv) 
    nts_29, // 130 - sload8: BYTE_ALOAD(riv,riv) 
    nts_29, // 131 - r: UBYTE_LOAD(riv,riv) 
    nts_29, // 132 - uload8: UBYTE_LOAD(riv,riv) 
    nts_29, // 133 - r: UBYTE_ALOAD(riv,riv) 
    nts_29, // 134 - uload8: UBYTE_ALOAD(riv,riv) 
    nts_29, // 135 - r: SHORT_LOAD(riv,riv) 
    nts_29, // 136 - sload16: SHORT_LOAD(riv,riv) 
    nts_29, // 137 - r: SHORT_ALOAD(riv,riv) 
    nts_29, // 138 - sload16: SHORT_ALOAD(riv,riv) 
    nts_29, // 139 - r: USHORT_LOAD(riv,riv) 
    nts_29, // 140 - uload16: USHORT_LOAD(riv,riv) 
    nts_29, // 141 - r: USHORT_ALOAD(riv,riv) 
    nts_29, // 142 - uload16: USHORT_ALOAD(riv,riv) 
    nts_29, // 143 - load32: INT_LOAD(riv,riv) 
    nts_29, // 144 - load32: INT_ALOAD(riv,riv) 
    nts_29, // 145 - load64: LONG_LOAD(riv,riv) 
    nts_29, // 146 - load64: LONG_ALOAD(riv,riv) 
    nts_38, // 147 - r: LONG_ADD(r,rlv) 
    nts_39, // 148 - r: LONG_ADD(r,load64) 
    nts_40, // 149 - r: LONG_ADD(load64,rlv) 
    nts_38, // 150 - r: LONG_AND(r,rlv) 
    nts_39, // 151 - r: LONG_AND(r,load64) 
    nts_40, // 152 - r: LONG_AND(load64,rlv) 
    nts_38, // 153 - stm: LONG_IFCMP(r,rlv) 
    nts_29, // 154 - r: LONG_LOAD(riv,riv) 
    nts_29, // 155 - r: LONG_ALOAD(riv,riv) 
    nts_38, // 156 - r: LONG_MUL(r,rlv) 
    nts_38, // 157 - r: LONG_OR(r,rlv) 
    nts_39, // 158 - r: LONG_OR(r,load64) 
    nts_40, // 159 - r: LONG_OR(load64,rlv) 
    nts_30, // 160 - r: LONG_SHL(rlv,riv) 
    nts_30, // 161 - r: LONG_SHR(rlv,riv) 
    nts_19, // 162 - r: LONG_SUB(rlv,rlv) 
    nts_41, // 163 - r: LONG_SUB(rlv,load64) 
    nts_40, // 164 - r: LONG_SUB(load64,rlv) 
    nts_30, // 165 - r: LONG_USHR(rlv,riv) 
    nts_38, // 166 - r: LONG_XOR(r,rlv) 
    nts_39, // 167 - r: LONG_XOR(r,load64) 
    nts_40, // 168 - r: LONG_XOR(load64,rlv) 
    nts_16, // 169 - r: FLOAT_ADD(r,r) 
    nts_42, // 170 - r: FLOAT_ADD(r,float_load) 
    nts_43, // 171 - r: FLOAT_ADD(float_load,r) 
    nts_16, // 172 - r: DOUBLE_ADD(r,r) 
    nts_44, // 173 - r: DOUBLE_ADD(r,double_load) 
    nts_45, // 174 - r: DOUBLE_ADD(double_load,r) 
    nts_16, // 175 - r: FLOAT_SUB(r,r) 
    nts_42, // 176 - r: FLOAT_SUB(r,float_load) 
    nts_16, // 177 - r: DOUBLE_SUB(r,r) 
    nts_44, // 178 - r: DOUBLE_SUB(r,double_load) 
    nts_16, // 179 - r: FLOAT_MUL(r,r) 
    nts_42, // 180 - r: FLOAT_MUL(r,float_load) 
    nts_43, // 181 - r: FLOAT_MUL(float_load,r) 
    nts_16, // 182 - r: DOUBLE_MUL(r,r) 
    nts_44, // 183 - r: DOUBLE_MUL(r,double_load) 
    nts_45, // 184 - r: DOUBLE_MUL(double_load,r) 
    nts_16, // 185 - r: FLOAT_DIV(r,r) 
    nts_42, // 186 - r: FLOAT_DIV(r,float_load) 
    nts_16, // 187 - r: DOUBLE_DIV(r,r) 
    nts_44, // 188 - r: DOUBLE_DIV(r,double_load) 
    nts_16, // 189 - r: FLOAT_REM(r,r) 
    nts_16, // 190 - r: DOUBLE_REM(r,r) 
    nts_29, // 191 - r: DOUBLE_LOAD(riv,riv) 
    nts_46, // 192 - r: DOUBLE_LOAD(riv,rlv) 
    nts_19, // 193 - r: DOUBLE_LOAD(rlv,rlv) 
    nts_29, // 194 - double_load: DOUBLE_LOAD(riv,riv) 
    nts_29, // 195 - r: DOUBLE_ALOAD(riv,riv) 
    nts_30, // 196 - r: DOUBLE_ALOAD(rlv,riv) 
    nts_19, // 197 - double_load: DOUBLE_LOAD(rlv,rlv) 
    nts_36, // 198 - r: DOUBLE_ALOAD(riv,r) 
    nts_19, // 199 - r: DOUBLE_ALOAD(rlv,rlv) 
    nts_30, // 200 - double_load: DOUBLE_ALOAD(rlv,riv) 
    nts_29, // 201 - double_load: DOUBLE_ALOAD(riv,riv) 
    nts_29, // 202 - r: FLOAT_LOAD(riv,riv) 
    nts_19, // 203 - r: FLOAT_LOAD(rlv,rlv) 
    nts_29, // 204 - float_load: FLOAT_LOAD(riv,riv) 
    nts_30, // 205 - float_load: FLOAT_ALOAD(rlv,riv) 
    nts_29, // 206 - r: FLOAT_ALOAD(riv,riv) 
    nts_30, // 207 - r: FLOAT_ALOAD(rlv,riv) 
    nts_36, // 208 - r: FLOAT_ALOAD(riv,r) 
    nts_19, // 209 - r: FLOAT_ALOAD(rlv,rlv) 
    nts_29, // 210 - float_load: FLOAT_ALOAD(riv,riv) 
    nts_16, // 211 - stm: FLOAT_IFCMP(r,r) 
    nts_42, // 212 - stm: FLOAT_IFCMP(r,float_load) 
    nts_43, // 213 - stm: FLOAT_IFCMP(float_load,r) 
    nts_16, // 214 - stm: DOUBLE_IFCMP(r,r) 
    nts_44, // 215 - stm: DOUBLE_IFCMP(r,double_load) 
    nts_45, // 216 - stm: DOUBLE_IFCMP(double_load,r) 
    nts_0,  // 217 - stm: LOWTABLESWITCH(r) 
    nts_3,  // 218 - stm: NULL_CHECK(riv) 
    nts_0,  // 219 - stm: SET_CAUGHT_EXCEPTION(r) 
    nts_0,  // 220 - stm: TRAP_IF(r,INT_CONSTANT) 
    nts_0,  // 221 - stm: TRAP_IF(r,LONG_CONSTANT) 
    nts_47, // 222 - uload8: INT_AND(load8_16_32,INT_CONSTANT) 
    nts_47, // 223 - r: INT_AND(load8_16_32,INT_CONSTANT) 
    nts_47, // 224 - r: INT_2BYTE(load8_16_32) 
    nts_12, // 225 - r: INT_AND(load16_32,INT_CONSTANT) 
    nts_0,  // 226 - stm: PREFETCH(r) 
    nts_0,  // 227 - stm: RETURN(r) 
    nts_48, // 228 - address: INT_MOVE(address) 
    nts_4,  // 229 - address: INT_ADD(address1scaledreg,INT_CONSTANT) 
    nts_0,  // 230 - address1reg: INT_ADD(r,INT_CONSTANT) 
    nts_0,  // 231 - address1reg: INT_MOVE(r) 
    nts_5,  // 232 - address1reg: INT_MOVE(address1reg) 
    nts_5,  // 233 - address1reg: INT_ADD(address1reg,INT_CONSTANT) 
    nts_4,  // 234 - address1scaledreg: INT_MOVE(address1scaledreg) 
    nts_0,  // 235 - address1scaledreg: INT_SHL(r,INT_CONSTANT) 
    nts_4,  // 236 - address1scaledreg: INT_ADD(address1scaledreg,INT_CONSTANT) 
    nts_0,  // 237 - r: ADDR_2LONG(r) 
    nts_11, // 238 - r: ADDR_2LONG(load32) 
    nts_0,  // 239 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_0,  // 240 - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_0,  // 241 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_11, // 242 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) 
    nts_0,  // 243 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_11, // 244 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) 
    nts_49, // 245 - r: BOOLEAN_CMP_INT(cz,INT_CONSTANT) 
    nts_49, // 246 - boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT) 
    nts_50, // 247 - r: BOOLEAN_CMP_INT(szp,INT_CONSTANT) 
    nts_50, // 248 - boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT) 
    nts_51, // 249 - r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) 
    nts_51, // 250 - boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) 
    nts_52, // 251 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_52, // 252 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_52, // 253 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_52, // 254 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_0,  // 255 - r: BOOLEAN_NOT(r) 
    nts_0,  // 256 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_11, // 257 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_0,  // 258 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_11, // 259 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_0,  // 260 - r: INT_2BYTE(r) 
    nts_47, // 261 - r: INT_2BYTE(load8_16_32) 
    nts_0,  // 262 - r: INT_2LONG(r) 
    nts_11, // 263 - r: INT_2LONG(load32) 
    nts_0,  // 264 - r: INT_2SHORT(r) 
    nts_12, // 265 - r: INT_2SHORT(load16_32) 
    nts_12, // 266 - sload16: INT_2SHORT(load16_32) 
    nts_0,  // 267 - szpr: INT_2USHORT(r) 
    nts_12, // 268 - uload16: INT_2USHORT(load16_32) 
    nts_12, // 269 - r: INT_2USHORT(load16_32) 
    nts_0,  // 270 - stm: INT_IFCMP(r,INT_CONSTANT) 
    nts_13, // 271 - stm: INT_IFCMP(load8,INT_CONSTANT) 
    nts_8,  // 272 - stm: INT_IFCMP(sload16,INT_CONSTANT) 
    nts_52, // 273 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) 
    nts_52, // 274 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) 
    nts_49, // 275 - stm: INT_IFCMP(cz,INT_CONSTANT) 
    nts_50, // 276 - stm: INT_IFCMP(szp,INT_CONSTANT) 
    nts_51, // 277 - stm: INT_IFCMP(bittest,INT_CONSTANT) 
    nts_48, // 278 - r: INT_LOAD(address,INT_CONSTANT) 
    nts_3,  // 279 - r: INT_MOVE(riv) 
    nts_1,  // 280 - czr: INT_MOVE(czr) 
    nts_49, // 281 - cz: INT_MOVE(cz) 
    nts_2,  // 282 - szpr: INT_MOVE(szpr) 
    nts_50, // 283 - szp: INT_MOVE(szp) 
    nts_6,  // 284 - sload8: INT_MOVE(sload8) 
    nts_7,  // 285 - uload8: INT_MOVE(uload8) 
    nts_13, // 286 - load8: INT_MOVE(load8) 
    nts_8,  // 287 - sload16: INT_MOVE(sload16) 
    nts_9,  // 288 - uload16: INT_MOVE(uload16) 
    nts_10, // 289 - load16: INT_MOVE(load16) 
    nts_11, // 290 - load32: INT_MOVE(load32) 
    nts_0,  // 291 - szpr: INT_NEG(r) 
    nts_0,  // 292 - r: INT_NOT(r) 
    nts_0,  // 293 - szpr: INT_SHL(r,INT_CONSTANT) 
    nts_0,  // 294 - r: INT_SHL(r,INT_CONSTANT) 
    nts_3,  // 295 - szpr: INT_SHR(riv,INT_CONSTANT) 
    nts_3,  // 296 - szpr: INT_USHR(riv,INT_CONSTANT) 
    nts_48, // 297 - r: INT_ADD(address,INT_CONSTANT) 
    nts_48, // 298 - r: INT_MOVE(address) 
    nts_0,  // 299 - r: LONG_2INT(r) 
    nts_53, // 300 - r: LONG_2INT(load64) 
    nts_53, // 301 - load32: LONG_2INT(load64) 
    nts_0,  // 302 - r: LONG_MOVE(r) 
    nts_53, // 303 - load64: LONG_MOVE(load64) 
    nts_0,  // 304 - r: LONG_NEG(r) 
    nts_0,  // 305 - r: LONG_NOT(r) 
    nts_0,  // 306 - r: FLOAT_NEG(r) 
    nts_0,  // 307 - r: DOUBLE_NEG(r) 
    nts_0,  // 308 - r: FLOAT_SQRT(r) 
    nts_0,  // 309 - r: DOUBLE_SQRT(r) 
    nts_0,  // 310 - r: LONG_2FLOAT(r) 
    nts_0,  // 311 - r: LONG_2DOUBLE(r) 
    nts_0,  // 312 - r: FLOAT_MOVE(r) 
    nts_0,  // 313 - r: DOUBLE_MOVE(r) 
    nts_3,  // 314 - r: INT_2FLOAT(riv) 
    nts_11, // 315 - r: INT_2FLOAT(load32) 
    nts_3,  // 316 - r: INT_2DOUBLE(riv) 
    nts_11, // 317 - r: INT_2DOUBLE(load32) 
    nts_0,  // 318 - r: FLOAT_2DOUBLE(r) 
    nts_54, // 319 - r: FLOAT_2DOUBLE(float_load) 
    nts_0,  // 320 - r: DOUBLE_2FLOAT(r) 
    nts_55, // 321 - r: DOUBLE_2FLOAT(double_load) 
    nts_0,  // 322 - r: FLOAT_2INT(r) 
    nts_0,  // 323 - r: FLOAT_2LONG(r) 
    nts_0,  // 324 - r: DOUBLE_2INT(r) 
    nts_0,  // 325 - r: DOUBLE_2LONG(r) 
    nts_0,  // 326 - r: FLOAT_AS_INT_BITS(r) 
    nts_54, // 327 - load32: FLOAT_AS_INT_BITS(float_load) 
    nts_0,  // 328 - r: DOUBLE_AS_LONG_BITS(r) 
    nts_55, // 329 - load64: DOUBLE_AS_LONG_BITS(double_load) 
    nts_3,  // 330 - r: INT_BITS_AS_FLOAT(riv) 
    nts_11, // 331 - float_load: INT_BITS_AS_FLOAT(load32) 
    nts_56, // 332 - r: LONG_BITS_AS_DOUBLE(rlv) 
    nts_53, // 333 - double_load: LONG_BITS_AS_DOUBLE(load64) 
    nts_57, // 334 - r: MATERIALIZE_FP_CONSTANT(any) 
    nts_57, // 335 - float_load: MATERIALIZE_FP_CONSTANT(any) 
    nts_57, // 336 - double_load: MATERIALIZE_FP_CONSTANT(any) 
    nts_47, // 337 - r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT) 
    nts_12, // 338 - r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 339 - bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 340 - bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 341 - r: LONG_AND(INT_2LONG(r),LONG_CONSTANT) 
    nts_11, // 342 - r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT) 
    nts_0,  // 343 - r: LONG_SHL(INT_2LONG(r),INT_CONSTANT) 
    nts_53, // 344 - r: LONG_SHL(INT_2LONG(load64),INT_CONSTANT) 
    nts_0,  // 345 - szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 346 - r: LONG_2INT(LONG_USHR(r,INT_CONSTANT)) 
    nts_0,  // 347 - r: LONG_2INT(LONG_SHR(r,INT_CONSTANT)) 
    nts_53, // 348 - r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) 
    nts_53, // 349 - r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) 
    nts_53, // 350 - load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) 
    nts_53, // 351 - load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) 
    nts_56, // 352 - r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_CONSTANT) 
    nts_58, // 353 - stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_59, // 354 - stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv)) 
    nts_60, // 355 - stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv)) 
    nts_61, // 356 - stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv)) 
    nts_58, // 357 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_59, // 358 - stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv)) 
    nts_62, // 359 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r)) 
    nts_58, // 360 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_62, // 361 - stm: INT_ASTORE(riv,OTHER_OPERAND(r,r)) 
    nts_61, // 362 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv)) 
    nts_63, // 363 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv)) 
    nts_64, // 364 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv)) 
    nts_65, // 365 - stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv)) 
    nts_66, // 366 - stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_67, // 367 - stm: LONG_ASTORE(r,OTHER_OPERAND(r,r)) 
    nts_68, // 368 - stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv)) 
    nts_68, // 369 - stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv)) 
    nts_58, // 370 - stm: BYTE_STORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_69, // 371 - stm: BYTE_STORE(load8,OTHER_OPERAND(riv,riv)) 
    nts_58, // 372 - stm: BYTE_ASTORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_69, // 373 - stm: BYTE_ASTORE(load8,OTHER_OPERAND(riv,riv)) 
    nts_70, // 374 - r: CMP_CMOV(r,OTHER_OPERAND(riv,any)) 
    nts_71, // 375 - r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any)) 
    nts_72, // 376 - r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any)) 
    nts_73, // 377 - r: CMP_CMOV(load32,OTHER_OPERAND(riv,any)) 
    nts_74, // 378 - r: CMP_CMOV(riv,OTHER_OPERAND(load32,any)) 
    nts_58, // 379 - stm: INT_STORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_75, // 380 - stm: INT_STORE(riv,OTHER_OPERAND(riv,address1scaledreg)) 
    nts_76, // 381 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,riv)) 
    nts_77, // 382 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg)) 
    nts_78, // 383 - stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg)) 
    nts_79, // 384 - r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any)) 
    nts_65, // 385 - stm: LONG_STORE(r,OTHER_OPERAND(riv,riv)) 
    nts_65, // 386 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv)) 
    nts_80, // 387 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_81, // 388 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_66, // 389 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_65, // 390 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv)) 
    nts_81, // 391 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_80, // 392 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_66, // 393 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_67, // 394 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r)) 
    nts_65, // 395 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv)) 
    nts_66, // 396 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_81, // 397 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_80, // 398 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_65, // 399 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv)) 
    nts_81, // 400 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_80, // 401 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_66, // 402 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_67, // 403 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r)) 
    nts_82, // 404 - r: FCMP_CMOV(r,OTHER_OPERAND(r,any)) 
    nts_83, // 405 - r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any)) 
    nts_84, // 406 - r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any)) 
    nts_85, // 407 - r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any)) 
    nts_86, // 408 - r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any)) 
    nts_82, // 409 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,any)) 
    nts_83, // 410 - r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any)) 
    nts_84, // 411 - r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any)) 
    nts_87, // 412 - stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv)) 
    nts_88, // 413 - stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv)) 
    nts_87, // 414 - stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv)) 
    nts_88, // 415 - stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv)) 
    nts_29, // 416 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv)) 
    nts_30, // 417 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv)) 
    nts_29, // 418 - stm: LONG_STORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv)) 
    nts_57, // 419 - r: CALL(BRANCH_TARGET,any) 
    nts_57, // 420 - r: CALL(INT_CONSTANT,any) 
    nts_57, // 421 - r: SYSCALL(INT_CONSTANT,any) 
    nts_89, // 422 - r: CALL(INT_LOAD(riv,riv),any) 
    nts_90, // 423 - r: CALL(LONG_LOAD(rlv,rlv),any) 
    nts_89, // 424 - r: SYSCALL(INT_LOAD(riv,riv),any) 
    nts_91, // 425 - r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))) 
    nts_92, // 426 - r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) 
    nts_93, // 427 - r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) 
    nts_94, // 428 - r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) 
    nts_95, // 429 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))) 
    nts_96, // 430 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))) 
    nts_97, // 431 - r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) 
    nts_98, // 432 - r: ATTEMPT_LONG(riv,OTHER_OPERAND(riv,OTHER_OPERAND(rlv,rlv))) 
    nts_99, // 433 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load))) 
    nts_100, // 434 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load))) 
    nts_101, // 435 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r))) 
    nts_102, // 436 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r))) 
    nts_103, // 437 - r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))) 
    nts_103, // 438 - r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))) 
    nts_91, // 439 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_94, // 440 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_95, // 441 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_96, // 442 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_97, // 443 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_91, // 444 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_94, // 445 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_95, // 446 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_96, // 447 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_97, // 448 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_103, // 449 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_103, // 450 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_103, // 451 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_103, // 452 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_16, // 453 - bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_37, // 454 - bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_16, // 455 - bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_37, // 456 - bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_36, // 457 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r) 
    nts_26, // 458 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32) 
    nts_16, // 459 - bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) 
    nts_37, // 460 - bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) 
    nts_91, // 461 - stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 462 - stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 463 - stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 464 - stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 465 - stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 466 - stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 467 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_91, // 468 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_91, // 469 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_91, // 470 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_91, // 471 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_91, // 472 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_91, // 473 - stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 474 - stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 475 - stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_91, // 476 - stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_20, // 477 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_104, // 478 - r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_105, // 479 - r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_106, // 480 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_106, // 481 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_107, // 482 - r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_108, // 483 - r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_109, // 484 - r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_65, // 485 - stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 486 - stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 487 - stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 488 - stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 489 - stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 490 - stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 491 - stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) 
    nts_65, // 492 - stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) 
    nts_110, // 493 - stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 494 - stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 495 - stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 496 - stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 497 - stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 498 - stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 499 - stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 500 - stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 501 - stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_110, // 502 - stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_111, // 503 - stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 504 - stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 505 - stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 506 - stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 507 - stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 508 - stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 509 - stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 510 - stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 511 - stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_111, // 512 - stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_110, // 513 - stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_110, // 514 - stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_112, // 515 - stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_112, // 516 - stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_112, // 517 - stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_112, // 518 - stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_110, // 519 - stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_110, // 520 - stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_112, // 521 - stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_112, // 522 - stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_113, // 523 - stm: LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 524 - stm: LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 525 - stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 526 - stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 527 - stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 528 - stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 529 - stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_113, // 530 - stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_16, // 531 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) 
    nts_16, // 532 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) 
    nts_16, // 533 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) 
    nts_16, // 534 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) 
    nts_19, // 535 - r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_AND(rlv,LONG_CONSTANT)) 
    nts_29, // 536 - r: LONG_MUL(INT_2LONG(riv),INT_2LONG(riv)) 
    nts_114, // 537 - r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT))) 
    nts_114, // 538 - r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT))) 
    nts_114, // 539 - r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT))) 
    nts_114, // 540 - r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT))) 
    nts_36, // 541 - szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT)) 
    nts_36, // 542 - szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT)) 
    nts_115, // 543 - stm: INT_STORE(riv,OTHER_OPERAND(address,INT_CONSTANT)) 
    nts_36, // 544 - szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT)) 
    nts_30, // 545 - r: LONG_SHL(rlv,INT_AND(riv,INT_CONSTANT)) 
    nts_30, // 546 - r: LONG_SHR(rlv,INT_AND(riv,INT_CONSTANT)) 
    nts_30, // 547 - r: LONG_USHR(rlv,INT_AND(riv,INT_CONSTANT)) 
    nts_116, // 548 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_116, // 549 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_116, // 550 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_116, // 551 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_116, // 552 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_116, // 553 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_67, // 554 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_67, // 555 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_67, // 556 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
    nts_67, // 557 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
    nts_67, // 558 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_67, // 559 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_67, // 560 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_67, // 561 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_67, // 562 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_67, // 563 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_67, // 564 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_67, // 565 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_67, // 566 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_67, // 567 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_67, // 568 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
    nts_67, // 569 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
  };

  /* private static final byte arity[] = {
    0,  // 0 - GET_CAUGHT_EXCEPTION
    1,  // 1 - SET_CAUGHT_EXCEPTION
    -1, // 2 - NEW
    -1, // 3 - NEW_UNRESOLVED
    -1, // 4 - NEWARRAY
    -1, // 5 - NEWARRAY_UNRESOLVED
    -1, // 6 - ATHROW
    -1, // 7 - CHECKCAST
    -1, // 8 - CHECKCAST_NOTNULL
    -1, // 9 - CHECKCAST_UNRESOLVED
    -1, // 10 - MUST_IMPLEMENT_INTERFACE
    -1, // 11 - INSTANCEOF
    -1, // 12 - INSTANCEOF_NOTNULL
    -1, // 13 - INSTANCEOF_UNRESOLVED
    -1, // 14 - MONITORENTER
    -1, // 15 - MONITOREXIT
    -1, // 16 - NEWOBJMULTIARRAY
    -1, // 17 - GETSTATIC
    -1, // 18 - PUTSTATIC
    -1, // 19 - GETFIELD
    -1, // 20 - PUTFIELD
    -1, // 21 - INT_ZERO_CHECK
    -1, // 22 - LONG_ZERO_CHECK
    -1, // 23 - BOUNDS_CHECK
    -1, // 24 - OBJARRAY_STORE_CHECK
    -1, // 25 - OBJARRAY_STORE_CHECK_NOTNULL
    0,  // 26 - IG_PATCH_POINT
    -1, // 27 - IG_CLASS_TEST
    -1, // 28 - IG_METHOD_TEST
    -1, // 29 - TABLESWITCH
    -1, // 30 - LOOKUPSWITCH
    2,  // 31 - INT_ALOAD
    2,  // 32 - LONG_ALOAD
    2,  // 33 - FLOAT_ALOAD
    2,  // 34 - DOUBLE_ALOAD
    -1, // 35 - REF_ALOAD
    2,  // 36 - UBYTE_ALOAD
    2,  // 37 - BYTE_ALOAD
    2,  // 38 - USHORT_ALOAD
    2,  // 39 - SHORT_ALOAD
    2,  // 40 - INT_ASTORE
    2,  // 41 - LONG_ASTORE
    2,  // 42 - FLOAT_ASTORE
    2,  // 43 - DOUBLE_ASTORE
    -1, // 44 - REF_ASTORE
    2,  // 45 - BYTE_ASTORE
    2,  // 46 - SHORT_ASTORE
    2,  // 47 - INT_IFCMP
    2,  // 48 - INT_IFCMP2
    2,  // 49 - LONG_IFCMP
    2,  // 50 - FLOAT_IFCMP
    2,  // 51 - DOUBLE_IFCMP
    -1, // 52 - REF_IFCMP
    -1, // 53 - LABEL
    -1, // 54 - BBEND
    0,  // 55 - UNINT_BEGIN
    0,  // 56 - UNINT_END
    0,  // 57 - FENCE
    0,  // 58 - READ_CEILING
    0,  // 59 - WRITE_FLOOR
    -1, // 60 - PHI
    -1, // 61 - SPLIT
    -1, // 62 - PI
    0,  // 63 - NOP
    1,  // 64 - INT_MOVE
    1,  // 65 - LONG_MOVE
    1,  // 66 - FLOAT_MOVE
    1,  // 67 - DOUBLE_MOVE
    -1, // 68 - REF_MOVE
    0,  // 69 - GUARD_MOVE
    -1, // 70 - INT_COND_MOVE
    -1, // 71 - LONG_COND_MOVE
    -1, // 72 - FLOAT_COND_MOVE
    -1, // 73 - DOUBLE_COND_MOVE
    -1, // 74 - REF_COND_MOVE
    -1, // 75 - GUARD_COND_MOVE
    0,  // 76 - GUARD_COMBINE
    -1, // 77 - REF_ADD
    2,  // 78 - INT_ADD
    2,  // 79 - LONG_ADD
    2,  // 80 - FLOAT_ADD
    2,  // 81 - DOUBLE_ADD
    -1, // 82 - REF_SUB
    2,  // 83 - INT_SUB
    2,  // 84 - LONG_SUB
    2,  // 85 - FLOAT_SUB
    2,  // 86 - DOUBLE_SUB
    2,  // 87 - INT_MUL
    2,  // 88 - LONG_MUL
    2,  // 89 - FLOAT_MUL
    2,  // 90 - DOUBLE_MUL
    2,  // 91 - INT_DIV
    -1, // 92 - LONG_DIV
    2,  // 93 - UNSIGNED_DIV_64_32
    2,  // 94 - UNSIGNED_REM_64_32
    2,  // 95 - FLOAT_DIV
    2,  // 96 - DOUBLE_DIV
    2,  // 97 - INT_REM
    -1, // 98 - LONG_REM
    2,  // 99 - FLOAT_REM
    2,  // 100 - DOUBLE_REM
    -1, // 101 - REF_NEG
    1,  // 102 - INT_NEG
    1,  // 103 - LONG_NEG
    1,  // 104 - FLOAT_NEG
    1,  // 105 - DOUBLE_NEG
    1,  // 106 - FLOAT_SQRT
    1,  // 107 - DOUBLE_SQRT
    -1, // 108 - REF_SHL
    2,  // 109 - INT_SHL
    2,  // 110 - LONG_SHL
    -1, // 111 - REF_SHR
    2,  // 112 - INT_SHR
    2,  // 113 - LONG_SHR
    -1, // 114 - REF_USHR
    2,  // 115 - INT_USHR
    2,  // 116 - LONG_USHR
    -1, // 117 - REF_AND
    2,  // 118 - INT_AND
    2,  // 119 - LONG_AND
    -1, // 120 - REF_OR
    2,  // 121 - INT_OR
    2,  // 122 - LONG_OR
    -1, // 123 - REF_XOR
    2,  // 124 - INT_XOR
    -1, // 125 - REF_NOT
    1,  // 126 - INT_NOT
    1,  // 127 - LONG_NOT
    2,  // 128 - LONG_XOR
    -1, // 129 - INT_2ADDRSigExt
    -1, // 130 - INT_2ADDRZerExt
    -1, // 131 - LONG_2ADDR
    -1, // 132 - ADDR_2INT
    1,  // 133 - ADDR_2LONG
    1,  // 134 - INT_2LONG
    1,  // 135 - INT_2FLOAT
    1,  // 136 - INT_2DOUBLE
    1,  // 137 - LONG_2INT
    1,  // 138 - LONG_2FLOAT
    1,  // 139 - LONG_2DOUBLE
    1,  // 140 - FLOAT_2INT
    1,  // 141 - FLOAT_2LONG
    1,  // 142 - FLOAT_2DOUBLE
    1,  // 143 - DOUBLE_2INT
    1,  // 144 - DOUBLE_2LONG
    1,  // 145 - DOUBLE_2FLOAT
    1,  // 146 - INT_2BYTE
    1,  // 147 - INT_2USHORT
    1,  // 148 - INT_2SHORT
    2,  // 149 - LONG_CMP
    -1, // 150 - FLOAT_CMPL
    -1, // 151 - FLOAT_CMPG
    -1, // 152 - DOUBLE_CMPL
    -1, // 153 - DOUBLE_CMPG
    1,  // 154 - RETURN
    1,  // 155 - NULL_CHECK
    0,  // 156 - GOTO
    1,  // 157 - BOOLEAN_NOT
    2,  // 158 - BOOLEAN_CMP_INT
    -1, // 159 - BOOLEAN_CMP_ADDR
    2,  // 160 - BOOLEAN_CMP_LONG
    -1, // 161 - BOOLEAN_CMP_FLOAT
    -1, // 162 - BOOLEAN_CMP_DOUBLE
    2,  // 163 - BYTE_LOAD
    2,  // 164 - UBYTE_LOAD
    2,  // 165 - SHORT_LOAD
    2,  // 166 - USHORT_LOAD
    -1, // 167 - REF_LOAD
    -1, // 168 - REF_STORE
    2,  // 169 - INT_LOAD
    2,  // 170 - LONG_LOAD
    2,  // 171 - FLOAT_LOAD
    2,  // 172 - DOUBLE_LOAD
    2,  // 173 - BYTE_STORE
    2,  // 174 - SHORT_STORE
    2,  // 175 - INT_STORE
    2,  // 176 - LONG_STORE
    2,  // 177 - FLOAT_STORE
    2,  // 178 - DOUBLE_STORE
    -1, // 179 - PREPARE_INT
    -1, // 180 - PREPARE_ADDR
    -1, // 181 - PREPARE_LONG
    2,  // 182 - ATTEMPT_INT
    -1, // 183 - ATTEMPT_ADDR
    2,  // 184 - ATTEMPT_LONG
    2,  // 185 - CALL
    2,  // 186 - SYSCALL
    -1, // 187 - UNIMPLEMENTED_BUT_UNREACHABLE
    0,  // 188 - YIELDPOINT_PROLOGUE
    0,  // 189 - YIELDPOINT_EPILOGUE
    0,  // 190 - YIELDPOINT_BACKEDGE
    2,  // 191 - YIELDPOINT_OSR
    -1, // 192 - OSR_BARRIER
    0,  // 193 - IR_PROLOGUE
    0,  // 194 - RESOLVE
    -1, // 195 - RESOLVE_MEMBER
    0,  // 196 - GET_TIME_BASE
    -1, // 197 - INSTRUMENTED_EVENT_COUNTER
    2,  // 198 - TRAP_IF
    0,  // 199 - TRAP
    0,  // 200 - ILLEGAL_INSTRUCTION
    1,  // 201 - FLOAT_AS_INT_BITS
    1,  // 202 - INT_BITS_AS_FLOAT
    1,  // 203 - DOUBLE_AS_LONG_BITS
    1,  // 204 - LONG_BITS_AS_DOUBLE
    -1, // 205 - ARRAYLENGTH
    0,  // 206 - FRAMESIZE
    -1, // 207 - GET_OBJ_TIB
    -1, // 208 - GET_CLASS_TIB
    -1, // 209 - GET_TYPE_FROM_TIB
    -1, // 210 - GET_SUPERCLASS_IDS_FROM_TIB
    -1, // 211 - GET_DOES_IMPLEMENT_FROM_TIB
    -1, // 212 - GET_ARRAY_ELEMENT_TIB_FROM_TIB
    1,  // 213 - LOWTABLESWITCH
    0,  // 214 - ADDRESS_CONSTANT
    0,  // 215 - INT_CONSTANT
    0,  // 216 - LONG_CONSTANT
    0,  // 217 - REGISTER
    2,  // 218 - OTHER_OPERAND
    0,  // 219 - NULL
    0,  // 220 - BRANCH_TARGET
    1,  // 221 - MATERIALIZE_FP_CONSTANT
    -1, // 222 - ROUND_TO_ZERO
    0,  // 223 - CLEAR_FLOATING_POINT_STATE
    1,  // 224 - PREFETCH
    0,  // 225 - PAUSE
    -1, // 226 - FP_ADD
    -1, // 227 - FP_SUB
    -1, // 228 - FP_MUL
    -1, // 229 - FP_DIV
    -1, // 230 - FP_NEG
    -1, // 231 - FP_REM
    -1, // 232 - INT_2FP
    -1, // 233 - LONG_2FP
    2,  // 234 - CMP_CMOV
    2,  // 235 - FCMP_CMOV
    2,  // 236 - LCMP_CMOV
    -1, // 237 - CMP_FCMOV
    2,  // 238 - FCMP_FCMOV
    -1, // 239 - CALL_SAVE_VOLATILE
    -1, // 240 - MIR_START
    -1, // 241 - REQUIRE_ESP
    -1, // 242 - ADVISE_ESP
    -1, // 243 - MIR_LOWTABLESWITCH
    -1, // 244 - IA32_METHODSTART
    -1, // 245 - IA32_FCLEAR
    -1, // 246 - DUMMY_DEF
    -1, // 247 - DUMMY_USE
    -1, // 248 - IMMQ_MOV
    -1, // 249 - IA32_FMOV_ENDING_LIVE_RANGE
    -1, // 250 - IA32_FMOV
    -1, // 251 - IA32_TRAPIF
    -1, // 252 - IA32_OFFSET
    -1, // 253 - IA32_LOCK_CMPXCHG
    -1, // 254 - IA32_LOCK_CMPXCHG8B
    -1, // 255 - IA32_ADC
    -1, // 256 - IA32_ADD
    -1, // 257 - IA32_AND
    -1, // 258 - IA32_BSWAP
    -1, // 259 - IA32_BT
    -1, // 260 - IA32_BTC
    -1, // 261 - IA32_BTR
    -1, // 262 - IA32_BTS
    -1, // 263 - IA32_SYSCALL
    -1, // 264 - IA32_CALL
    -1, // 265 - IA32_CDQ
    -1, // 266 - IA32_CDO
    -1, // 267 - IA32_CDQE
    -1, // 268 - IA32_CMOV
    -1, // 269 - IA32_CMP
    -1, // 270 - IA32_CMPXCHG
    -1, // 271 - IA32_CMPXCHG8B
    -1, // 272 - IA32_DEC
    -1, // 273 - IA32_DIV
    -1, // 274 - IA32_FADD
    -1, // 275 - IA32_FADDP
    -1, // 276 - IA32_FCHS
    -1, // 277 - IA32_FCMOV
    -1, // 278 - IA32_FCOMI
    -1, // 279 - IA32_FCOMIP
    -1, // 280 - IA32_FDIV
    -1, // 281 - IA32_FDIVP
    -1, // 282 - IA32_FDIVR
    -1, // 283 - IA32_FDIVRP
    -1, // 284 - IA32_FEXAM
    -1, // 285 - IA32_FXCH
    -1, // 286 - IA32_FFREE
    -1, // 287 - IA32_FFREEP
    -1, // 288 - IA32_FIADD
    -1, // 289 - IA32_FIDIV
    -1, // 290 - IA32_FIDIVR
    -1, // 291 - IA32_FILD
    -1, // 292 - IA32_FIMUL
    -1, // 293 - IA32_FINIT
    -1, // 294 - IA32_FIST
    -1, // 295 - IA32_FISTP
    -1, // 296 - IA32_FISUB
    -1, // 297 - IA32_FISUBR
    -1, // 298 - IA32_FLD
    -1, // 299 - IA32_FLDCW
    -1, // 300 - IA32_FLD1
    -1, // 301 - IA32_FLDL2T
    -1, // 302 - IA32_FLDL2E
    -1, // 303 - IA32_FLDPI
    -1, // 304 - IA32_FLDLG2
    -1, // 305 - IA32_FLDLN2
    -1, // 306 - IA32_FLDZ
    -1, // 307 - IA32_FMUL
    -1, // 308 - IA32_FMULP
    -1, // 309 - IA32_FNSTCW
    -1, // 310 - IA32_FNSTSW
    -1, // 311 - IA32_FNINIT
    -1, // 312 - IA32_FNSAVE
    -1, // 313 - IA32_FPREM
    -1, // 314 - IA32_FRSTOR
    -1, // 315 - IA32_FST
    -1, // 316 - IA32_FSTCW
    -1, // 317 - IA32_FSTSW
    -1, // 318 - IA32_FSTP
    -1, // 319 - IA32_FSUB
    -1, // 320 - IA32_FSUBP
    -1, // 321 - IA32_FSUBR
    -1, // 322 - IA32_FSUBRP
    -1, // 323 - IA32_FUCOMI
    -1, // 324 - IA32_FUCOMIP
    -1, // 325 - IA32_IDIV
    -1, // 326 - IA32_IMUL1
    -1, // 327 - IA32_IMUL2
    -1, // 328 - IA32_INC
    -1, // 329 - IA32_INT
    -1, // 330 - IA32_JCC
    -1, // 331 - IA32_JCC2
    -1, // 332 - IA32_JMP
    -1, // 333 - IA32_LEA
    -1, // 334 - IA32_LOCK
    -1, // 335 - IA32_MOV
    -1, // 336 - IA32_MOVZX__B
    -1, // 337 - IA32_MOVSX__B
    -1, // 338 - IA32_MOVZX__W
    -1, // 339 - IA32_MOVSX__W
    -1, // 340 - IA32_MOVZXQ__B
    -1, // 341 - IA32_MOVSXQ__B
    -1, // 342 - IA32_MOVZXQ__W
    -1, // 343 - IA32_MOVSXQ__W
    -1, // 344 - IA32_MOVSXDQ
    -1, // 345 - IA32_MUL
    -1, // 346 - IA32_NEG
    -1, // 347 - IA32_NOT
    -1, // 348 - IA32_OR
    -1, // 349 - IA32_MFENCE
    -1, // 350 - IA32_PAUSE
    -1, // 351 - IA32_UD2
    -1, // 352 - IA32_PREFETCHNTA
    -1, // 353 - IA32_POP
    -1, // 354 - IA32_PUSH
    -1, // 355 - IA32_RCL
    -1, // 356 - IA32_RCR
    -1, // 357 - IA32_ROL
    -1, // 358 - IA32_ROR
    -1, // 359 - IA32_RET
    -1, // 360 - IA32_SAL
    -1, // 361 - IA32_SAR
    -1, // 362 - IA32_SHL
    -1, // 363 - IA32_SHR
    -1, // 364 - IA32_SBB
    -1, // 365 - IA32_SET__B
    -1, // 366 - IA32_SHLD
    -1, // 367 - IA32_SHRD
    -1, // 368 - IA32_SUB
    -1, // 369 - IA32_TEST
    -1, // 370 - IA32_XOR
    -1, // 371 - IA32_RDTSC
    -1, // 372 - IA32_ADDSS
    -1, // 373 - IA32_SUBSS
    -1, // 374 - IA32_MULSS
    -1, // 375 - IA32_DIVSS
    -1, // 376 - IA32_ADDSD
    -1, // 377 - IA32_SUBSD
    -1, // 378 - IA32_MULSD
    -1, // 379 - IA32_DIVSD
    -1, // 380 - IA32_ANDPS
    -1, // 381 - IA32_ANDPD
    -1, // 382 - IA32_ANDNPS
    -1, // 383 - IA32_ANDNPD
    -1, // 384 - IA32_ORPS
    -1, // 385 - IA32_ORPD
    -1, // 386 - IA32_XORPS
    -1, // 387 - IA32_XORPD
    -1, // 388 - IA32_UCOMISS
    -1, // 389 - IA32_UCOMISD
    -1, // 390 - IA32_CMPEQSS
    -1, // 391 - IA32_CMPLTSS
    -1, // 392 - IA32_CMPLESS
    -1, // 393 - IA32_CMPUNORDSS
    -1, // 394 - IA32_CMPNESS
    -1, // 395 - IA32_CMPNLTSS
    -1, // 396 - IA32_CMPNLESS
    -1, // 397 - IA32_CMPORDSS
    -1, // 398 - IA32_CMPEQSD
    -1, // 399 - IA32_CMPLTSD
    -1, // 400 - IA32_CMPLESD
    -1, // 401 - IA32_CMPUNORDSD
    -1, // 402 - IA32_CMPNESD
    -1, // 403 - IA32_CMPNLTSD
    -1, // 404 - IA32_CMPNLESD
    -1, // 405 - IA32_CMPORDSD
    -1, // 406 - IA32_MOVAPD
    -1, // 407 - IA32_MOVAPS
    -1, // 408 - IA32_MOVLPD
    -1, // 409 - IA32_MOVLPS
    -1, // 410 - IA32_MOVSS
    -1, // 411 - IA32_MOVSD
    -1, // 412 - IA32_MOVD
    -1, // 413 - IA32_MOVQ
    -1, // 414 - IA32_PSLLQ
    -1, // 415 - IA32_PSRLQ
    -1, // 416 - IA32_SQRTSS
    -1, // 417 - IA32_SQRTSD
    -1, // 418 - IA32_CVTSI2SS
    -1, // 419 - IA32_CVTSS2SD
    -1, // 420 - IA32_CVTSS2SI
    -1, // 421 - IA32_CVTTSS2SI
    -1, // 422 - IA32_CVTSI2SD
    -1, // 423 - IA32_CVTSD2SS
    -1, // 424 - IA32_CVTSD2SI
    -1, // 425 - IA32_CVTTSD2SI
    -1, // 426 - IA32_CVTSI2SDQ
    -1, // 427 - IA32_CVTSD2SIQ
    -1, // 428 - IA32_CVTTSD2SIQ
    -1, // 429 - MIR_END
  };*/

  /**
   * Decoding table. Translate the target non-terminal and minimal cost covering state encoding
   * non-terminal into the rule that produces the non-terminal.
   * The first index is the non-terminal that we wish to produce.
   * The second index is the state non-terminal associated with covering a tree
   * with minimal cost and is computed by jburg based on the non-terminal to be produced.
   * The value in the array is the rule number
   */
  private static final char[][] decode = {
    null, // [0][0]
    { // stm_NT
      0, // [1][0]
      1, // [1][1] - stm: r
      25, // [1][2] - stm: IG_PATCH_POINT
      26, // [1][3] - stm: UNINT_BEGIN
      27, // [1][4] - stm: UNINT_END
      28, // [1][5] - stm: YIELDPOINT_PROLOGUE
      29, // [1][6] - stm: YIELDPOINT_EPILOGUE
      30, // [1][7] - stm: YIELDPOINT_BACKEDGE
      217, // [1][8] - stm: LOWTABLESWITCH(r)
      32, // [1][9] - stm: RESOLVE
      33, // [1][10] - stm: NOP
      218, // [1][11] - stm: NULL_CHECK(riv)
      36, // [1][12] - stm: IR_PROLOGUE
      219, // [1][13] - stm: SET_CAUGHT_EXCEPTION(r)
      38, // [1][14] - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
      39, // [1][15] - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
      40, // [1][16] - stm: TRAP
      220, // [1][17] - stm: TRAP_IF(r,INT_CONSTANT)
      221, // [1][18] - stm: TRAP_IF(r,LONG_CONSTANT)
      54, // [1][19] - stm: TRAP_IF(r,r)
      55, // [1][20] - stm: TRAP_IF(load32,riv)
      56, // [1][21] - stm: TRAP_IF(riv,load32)
      353, // [1][22] - stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
      354, // [1][23] - stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
      355, // [1][24] - stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      356, // [1][25] - stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      357, // [1][26] - stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      358, // [1][27] - stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
      359, // [1][28] - stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
      360, // [1][29] - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      361, // [1][30] - stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
      362, // [1][31] - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
      363, // [1][32] - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      364, // [1][33] - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
      365, // [1][34] - stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
      366, // [1][35] - stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      367, // [1][36] - stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
      416, // [1][37] - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
      417, // [1][38] - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
      41, // [1][39] - stm: GOTO
      226, // [1][40] - stm: PREFETCH(r)
      42, // [1][41] - stm: WRITE_FLOOR
      43, // [1][42] - stm: READ_CEILING
      44, // [1][43] - stm: FENCE
      45, // [1][44] - stm: PAUSE
      46, // [1][45] - stm: ILLEGAL_INSTRUCTION
      47, // [1][46] - stm: RETURN(NULL)
      48, // [1][47] - stm: RETURN(INT_CONSTANT)
      227, // [1][48] - stm: RETURN(r)
      49, // [1][49] - stm: RETURN(LONG_CONSTANT)
      60, // [1][50] - stm: YIELDPOINT_OSR(any,any)
      439, // [1][51] - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      440, // [1][52] - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      441, // [1][53] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      442, // [1][54] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      443, // [1][55] - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      449, // [1][56] - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      451, // [1][57] - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      444, // [1][58] - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      445, // [1][59] - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      446, // [1][60] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      447, // [1][61] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      448, // [1][62] - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      450, // [1][63] - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      452, // [1][64] - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      368, // [1][65] - stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
      369, // [1][66] - stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
      461, // [1][67] - stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      462, // [1][68] - stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      370, // [1][69] - stm: BYTE_STORE(riv,OTHER_OPERAND(riv,riv))
      371, // [1][70] - stm: BYTE_STORE(load8,OTHER_OPERAND(riv,riv))
      372, // [1][71] - stm: BYTE_ASTORE(riv,OTHER_OPERAND(riv,riv))
      373, // [1][72] - stm: BYTE_ASTORE(load8,OTHER_OPERAND(riv,riv))
      485, // [1][73] - stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      486, // [1][74] - stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      487, // [1][75] - stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      488, // [1][76] - stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      489, // [1][77] - stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      490, // [1][78] - stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      493, // [1][79] - stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      513, // [1][80] - stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      494, // [1][81] - stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      514, // [1][82] - stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      495, // [1][83] - stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      515, // [1][84] - stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      496, // [1][85] - stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      516, // [1][86] - stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      88, // [1][87] - stm: INT_IFCMP(r,riv)
      270, // [1][88] - stm: INT_IFCMP(r,INT_CONSTANT)
      271, // [1][89] - stm: INT_IFCMP(load8,INT_CONSTANT)
      89, // [1][90] - stm: INT_IFCMP(uload8,r)
      90, // [1][91] - stm: INT_IFCMP(r,uload8)
      272, // [1][92] - stm: INT_IFCMP(sload16,INT_CONSTANT)
      91, // [1][93] - stm: INT_IFCMP(load32,riv)
      92, // [1][94] - stm: INT_IFCMP(r,load32)
      273, // [1][95] - stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      274, // [1][96] - stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      275, // [1][97] - stm: INT_IFCMP(cz,INT_CONSTANT)
      276, // [1][98] - stm: INT_IFCMP(szp,INT_CONSTANT)
      277, // [1][99] - stm: INT_IFCMP(bittest,INT_CONSTANT)
      93, // [1][100] - stm: INT_IFCMP2(r,riv)
      94, // [1][101] - stm: INT_IFCMP2(load32,riv)
      95, // [1][102] - stm: INT_IFCMP2(riv,load32)
      463, // [1][103] - stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      464, // [1][104] - stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      465, // [1][105] - stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      466, // [1][106] - stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      497, // [1][107] - stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      517, // [1][108] - stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      498, // [1][109] - stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      518, // [1][110] - stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      548, // [1][111] - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      467, // [1][112] - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      549, // [1][113] - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      468, // [1][114] - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      550, // [1][115] - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      469, // [1][116] - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      551, // [1][117] - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      470, // [1][118] - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      379, // [1][119] - stm: INT_STORE(riv,OTHER_OPERAND(riv,riv))
      380, // [1][120] - stm: INT_STORE(riv,OTHER_OPERAND(riv,address1scaledreg))
      381, // [1][121] - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,riv))
      382, // [1][122] - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
      383, // [1][123] - stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
      543, // [1][124] - stm: INT_STORE(riv,OTHER_OPERAND(address,INT_CONSTANT))
      499, // [1][125] - stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      519, // [1][126] - stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      500, // [1][127] - stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      520, // [1][128] - stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      552, // [1][129] - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      471, // [1][130] - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      553, // [1][131] - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      472, // [1][132] - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      501, // [1][133] - stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      521, // [1][134] - stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      502, // [1][135] - stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      522, // [1][136] - stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      491, // [1][137] - stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      492, // [1][138] - stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      503, // [1][139] - stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      523, // [1][140] - stm: LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      504, // [1][141] - stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      524, // [1][142] - stm: LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      505, // [1][143] - stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      525, // [1][144] - stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      506, // [1][145] - stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      526, // [1][146] - stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      153, // [1][147] - stm: LONG_IFCMP(r,rlv)
      473, // [1][148] - stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      474, // [1][149] - stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      475, // [1][150] - stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      476, // [1][151] - stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      507, // [1][152] - stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      527, // [1][153] - stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      508, // [1][154] - stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      528, // [1][155] - stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      385, // [1][156] - stm: LONG_STORE(r,OTHER_OPERAND(riv,riv))
      418, // [1][157] - stm: LONG_STORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
      509, // [1][158] - stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      510, // [1][159] - stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      511, // [1][160] - stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      529, // [1][161] - stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      512, // [1][162] - stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      530, // [1][163] - stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      386, // [1][164] - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
      387, // [1][165] - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
      388, // [1][166] - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
      389, // [1][167] - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
      390, // [1][168] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
      391, // [1][169] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
      392, // [1][170] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
      393, // [1][171] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      394, // [1][172] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
      395, // [1][173] - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
      396, // [1][174] - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
      397, // [1][175] - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
      398, // [1][176] - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
      399, // [1][177] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
      400, // [1][178] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
      401, // [1][179] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
      402, // [1][180] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      403, // [1][181] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
      52, // [1][182] - stm: CLEAR_FLOATING_POINT_STATE
      211, // [1][183] - stm: FLOAT_IFCMP(r,r)
      212, // [1][184] - stm: FLOAT_IFCMP(r,float_load)
      213, // [1][185] - stm: FLOAT_IFCMP(float_load,r)
      214, // [1][186] - stm: DOUBLE_IFCMP(r,r)
      215, // [1][187] - stm: DOUBLE_IFCMP(r,double_load)
      216, // [1][188] - stm: DOUBLE_IFCMP(double_load,r)
      412, // [1][189] - stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
      413, // [1][190] - stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
      414, // [1][191] - stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
      415, // [1][192] - stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
    },
    { // r_NT
      0, // [2][0]
      19, // [2][1] - r: REGISTER
      2, // [2][2] - r: czr
      4, // [2][3] - r: szpr
      31, // [2][4] - r: FRAMESIZE
      34, // [2][5] - r: GUARD_MOVE
      35, // [2][6] - r: GUARD_COMBINE
      37, // [2][7] - r: GET_CAUGHT_EXCEPTION
      223, // [2][8] - r: INT_AND(load8_16_32,INT_CONSTANT)
      224, // [2][9] - r: INT_2BYTE(load8_16_32)
      337, // [2][10] - r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
      225, // [2][11] - r: INT_AND(load16_32,INT_CONSTANT)
      338, // [2][12] - r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
      57, // [2][13] - r: LONG_CMP(rlv,rlv)
      58, // [2][14] - r: CALL(r,any)
      419, // [2][15] - r: CALL(BRANCH_TARGET,any)
      422, // [2][16] - r: CALL(INT_LOAD(riv,riv),any)
      420, // [2][17] - r: CALL(INT_CONSTANT,any)
      423, // [2][18] - r: CALL(LONG_LOAD(rlv,rlv),any)
      59, // [2][19] - r: SYSCALL(r,any)
      424, // [2][20] - r: SYSCALL(INT_LOAD(riv,riv),any)
      421, // [2][21] - r: SYSCALL(INT_CONSTANT,any)
      50, // [2][22] - r: GET_TIME_BASE
      237, // [2][23] - r: ADDR_2LONG(r)
      238, // [2][24] - r: ADDR_2LONG(load32)
      425, // [2][25] - r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
      426, // [2][26] - r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      427, // [2][27] - r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      428, // [2][28] - r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      429, // [2][29] - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
      430, // [2][30] - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
      431, // [2][31] - r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      437, // [2][32] - r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
      438, // [2][33] - r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
      432, // [2][34] - r: ATTEMPT_LONG(riv,OTHER_OPERAND(riv,OTHER_OPERAND(rlv,rlv)))
      66, // [2][35] - r: BOOLEAN_CMP_INT(r,riv)
      239, // [2][36] - r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      241, // [2][37] - r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      242, // [2][38] - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      243, // [2][39] - r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      244, // [2][40] - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      245, // [2][41] - r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      247, // [2][42] - r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      249, // [2][43] - r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      251, // [2][44] - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      253, // [2][45] - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      68, // [2][46] - r: BOOLEAN_CMP_INT(load32,riv)
      70, // [2][47] - r: BOOLEAN_CMP_INT(r,load32)
      72, // [2][48] - r: BOOLEAN_CMP_LONG(rlv,rlv)
      255, // [2][49] - r: BOOLEAN_NOT(r)
      374, // [2][50] - r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
      477, // [2][51] - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      256, // [2][52] - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      257, // [2][53] - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      258, // [2][54] - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      259, // [2][55] - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      478, // [2][56] - r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
      375, // [2][57] - r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
      376, // [2][58] - r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
      479, // [2][59] - r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
      377, // [2][60] - r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
      378, // [2][61] - r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
      480, // [2][62] - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      481, // [2][63] - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      482, // [2][64] - r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
      483, // [2][65] - r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
      484, // [2][66] - r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
      260, // [2][67] - r: INT_2BYTE(r)
      261, // [2][68] - r: INT_2BYTE(load8_16_32)
      262, // [2][69] - r: INT_2LONG(r)
      263, // [2][70] - r: INT_2LONG(load32)
      341, // [2][71] - r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
      342, // [2][72] - r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
      343, // [2][73] - r: LONG_SHL(INT_2LONG(r),INT_CONSTANT)
      344, // [2][74] - r: LONG_SHL(INT_2LONG(load64),INT_CONSTANT)
      264, // [2][75] - r: INT_2SHORT(r)
      265, // [2][76] - r: INT_2SHORT(load16_32)
      269, // [2][77] - r: INT_2USHORT(load16_32)
      75, // [2][78] - r: INT_ADD(r,riv)
      84, // [2][79] - r: INT_DIV(riv,riv)
      85, // [2][80] - r: INT_DIV(riv,load32)
      86, // [2][81] - r: UNSIGNED_DIV_64_32(rlv,riv)
      87, // [2][82] - r: UNSIGNED_DIV_64_32(rlv,load32)
      96, // [2][83] - r: INT_LOAD(riv,riv)
      97, // [2][84] - r: INT_LOAD(riv,address1scaledreg)
      98, // [2][85] - r: INT_LOAD(address1scaledreg,riv)
      99, // [2][86] - r: INT_LOAD(address1scaledreg,address1reg)
      100, // [2][87] - r: INT_LOAD(address1reg,address1scaledreg)
      278, // [2][88] - r: INT_LOAD(address,INT_CONSTANT)
      101, // [2][89] - r: INT_ALOAD(riv,riv)
      279, // [2][90] - r: INT_MOVE(riv)
      102, // [2][91] - r: INT_MUL(r,riv)
      103, // [2][92] - r: INT_MUL(r,load32)
      104, // [2][93] - r: INT_MUL(load32,riv)
      292, // [2][94] - r: INT_NOT(r)
      108, // [2][95] - r: INT_REM(riv,riv)
      109, // [2][96] - r: INT_REM(riv,load32)
      110, // [2][97] - r: UNSIGNED_REM_64_32(rlv,riv)
      111, // [2][98] - r: UNSIGNED_REM_64_32(rlv,load32)
      531, // [2][99] - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      532, // [2][100] - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      533, // [2][101] - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      534, // [2][102] - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      537, // [2][103] - r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      539, // [2][104] - r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
      540, // [2][105] - r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
      538, // [2][106] - r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      294, // [2][107] - r: INT_SHL(r,INT_CONSTANT)
      115, // [2][108] - r: INT_SUB(riv,r)
      116, // [2][109] - r: INT_SUB(load32,r)
      384, // [2][110] - r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
      123, // [2][111] - r: INT_ADD(address1scaledreg,r)
      124, // [2][112] - r: INT_ADD(r,address1scaledreg)
      125, // [2][113] - r: INT_ADD(address1scaledreg,address1reg)
      126, // [2][114] - r: INT_ADD(address1reg,address1scaledreg)
      297, // [2][115] - r: INT_ADD(address,INT_CONSTANT)
      298, // [2][116] - r: INT_MOVE(address)
      127, // [2][117] - r: BYTE_LOAD(riv,riv)
      129, // [2][118] - r: BYTE_ALOAD(riv,riv)
      131, // [2][119] - r: UBYTE_LOAD(riv,riv)
      133, // [2][120] - r: UBYTE_ALOAD(riv,riv)
      135, // [2][121] - r: SHORT_LOAD(riv,riv)
      137, // [2][122] - r: SHORT_ALOAD(riv,riv)
      139, // [2][123] - r: USHORT_LOAD(riv,riv)
      141, // [2][124] - r: USHORT_ALOAD(riv,riv)
      299, // [2][125] - r: LONG_2INT(r)
      300, // [2][126] - r: LONG_2INT(load64)
      346, // [2][127] - r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
      347, // [2][128] - r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
      348, // [2][129] - r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      349, // [2][130] - r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      147, // [2][131] - r: LONG_ADD(r,rlv)
      148, // [2][132] - r: LONG_ADD(r,load64)
      149, // [2][133] - r: LONG_ADD(load64,rlv)
      150, // [2][134] - r: LONG_AND(r,rlv)
      151, // [2][135] - r: LONG_AND(r,load64)
      152, // [2][136] - r: LONG_AND(load64,rlv)
      154, // [2][137] - r: LONG_LOAD(riv,riv)
      155, // [2][138] - r: LONG_ALOAD(riv,riv)
      302, // [2][139] - r: LONG_MOVE(r)
      51, // [2][140] - r: LONG_MOVE(LONG_CONSTANT)
      156, // [2][141] - r: LONG_MUL(r,rlv)
      535, // [2][142] - r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_AND(rlv,LONG_CONSTANT))
      352, // [2][143] - r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_CONSTANT)
      536, // [2][144] - r: LONG_MUL(INT_2LONG(riv),INT_2LONG(riv))
      304, // [2][145] - r: LONG_NEG(r)
      305, // [2][146] - r: LONG_NOT(r)
      157, // [2][147] - r: LONG_OR(r,rlv)
      158, // [2][148] - r: LONG_OR(r,load64)
      159, // [2][149] - r: LONG_OR(load64,rlv)
      160, // [2][150] - r: LONG_SHL(rlv,riv)
      545, // [2][151] - r: LONG_SHL(rlv,INT_AND(riv,INT_CONSTANT))
      161, // [2][152] - r: LONG_SHR(rlv,riv)
      546, // [2][153] - r: LONG_SHR(rlv,INT_AND(riv,INT_CONSTANT))
      162, // [2][154] - r: LONG_SUB(rlv,rlv)
      163, // [2][155] - r: LONG_SUB(rlv,load64)
      164, // [2][156] - r: LONG_SUB(load64,rlv)
      165, // [2][157] - r: LONG_USHR(rlv,riv)
      547, // [2][158] - r: LONG_USHR(rlv,INT_AND(riv,INT_CONSTANT))
      166, // [2][159] - r: LONG_XOR(r,rlv)
      167, // [2][160] - r: LONG_XOR(r,load64)
      168, // [2][161] - r: LONG_XOR(load64,rlv)
      169, // [2][162] - r: FLOAT_ADD(r,r)
      170, // [2][163] - r: FLOAT_ADD(r,float_load)
      171, // [2][164] - r: FLOAT_ADD(float_load,r)
      172, // [2][165] - r: DOUBLE_ADD(r,r)
      173, // [2][166] - r: DOUBLE_ADD(r,double_load)
      174, // [2][167] - r: DOUBLE_ADD(double_load,r)
      175, // [2][168] - r: FLOAT_SUB(r,r)
      176, // [2][169] - r: FLOAT_SUB(r,float_load)
      177, // [2][170] - r: DOUBLE_SUB(r,r)
      178, // [2][171] - r: DOUBLE_SUB(r,double_load)
      179, // [2][172] - r: FLOAT_MUL(r,r)
      180, // [2][173] - r: FLOAT_MUL(r,float_load)
      181, // [2][174] - r: FLOAT_MUL(float_load,r)
      182, // [2][175] - r: DOUBLE_MUL(r,r)
      183, // [2][176] - r: DOUBLE_MUL(r,double_load)
      184, // [2][177] - r: DOUBLE_MUL(double_load,r)
      185, // [2][178] - r: FLOAT_DIV(r,r)
      186, // [2][179] - r: FLOAT_DIV(r,float_load)
      187, // [2][180] - r: DOUBLE_DIV(r,r)
      188, // [2][181] - r: DOUBLE_DIV(r,double_load)
      306, // [2][182] - r: FLOAT_NEG(r)
      307, // [2][183] - r: DOUBLE_NEG(r)
      308, // [2][184] - r: FLOAT_SQRT(r)
      309, // [2][185] - r: DOUBLE_SQRT(r)
      189, // [2][186] - r: FLOAT_REM(r,r)
      190, // [2][187] - r: DOUBLE_REM(r,r)
      310, // [2][188] - r: LONG_2FLOAT(r)
      311, // [2][189] - r: LONG_2DOUBLE(r)
      312, // [2][190] - r: FLOAT_MOVE(r)
      313, // [2][191] - r: DOUBLE_MOVE(r)
      191, // [2][192] - r: DOUBLE_LOAD(riv,riv)
      192, // [2][193] - r: DOUBLE_LOAD(riv,rlv)
      193, // [2][194] - r: DOUBLE_LOAD(rlv,rlv)
      195, // [2][195] - r: DOUBLE_ALOAD(riv,riv)
      196, // [2][196] - r: DOUBLE_ALOAD(rlv,riv)
      198, // [2][197] - r: DOUBLE_ALOAD(riv,r)
      199, // [2][198] - r: DOUBLE_ALOAD(rlv,rlv)
      202, // [2][199] - r: FLOAT_LOAD(riv,riv)
      203, // [2][200] - r: FLOAT_LOAD(rlv,rlv)
      206, // [2][201] - r: FLOAT_ALOAD(riv,riv)
      207, // [2][202] - r: FLOAT_ALOAD(rlv,riv)
      208, // [2][203] - r: FLOAT_ALOAD(riv,r)
      209, // [2][204] - r: FLOAT_ALOAD(rlv,rlv)
      314, // [2][205] - r: INT_2FLOAT(riv)
      315, // [2][206] - r: INT_2FLOAT(load32)
      316, // [2][207] - r: INT_2DOUBLE(riv)
      317, // [2][208] - r: INT_2DOUBLE(load32)
      318, // [2][209] - r: FLOAT_2DOUBLE(r)
      319, // [2][210] - r: FLOAT_2DOUBLE(float_load)
      320, // [2][211] - r: DOUBLE_2FLOAT(r)
      321, // [2][212] - r: DOUBLE_2FLOAT(double_load)
      322, // [2][213] - r: FLOAT_2INT(r)
      323, // [2][214] - r: FLOAT_2LONG(r)
      324, // [2][215] - r: DOUBLE_2INT(r)
      325, // [2][216] - r: DOUBLE_2LONG(r)
      326, // [2][217] - r: FLOAT_AS_INT_BITS(r)
      328, // [2][218] - r: DOUBLE_AS_LONG_BITS(r)
      330, // [2][219] - r: INT_BITS_AS_FLOAT(riv)
      332, // [2][220] - r: LONG_BITS_AS_DOUBLE(rlv)
      334, // [2][221] - r: MATERIALIZE_FP_CONSTANT(any)
      404, // [2][222] - r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
      405, // [2][223] - r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
      406, // [2][224] - r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
      407, // [2][225] - r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
      408, // [2][226] - r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
      409, // [2][227] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
      433, // [2][228] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
      434, // [2][229] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
      435, // [2][230] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
      436, // [2][231] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
      410, // [2][232] - r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
      411, // [2][233] - r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
      554, // [2][234] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      555, // [2][235] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      558, // [2][236] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      559, // [2][237] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      562, // [2][238] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      563, // [2][239] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      566, // [2][240] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      567, // [2][241] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      556, // [2][242] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      557, // [2][243] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      560, // [2][244] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      561, // [2][245] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      564, // [2][246] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      565, // [2][247] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      568, // [2][248] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      569, // [2][249] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
    },
    { // czr_NT
      0, // [3][0]
      74, // [3][1] - czr: INT_ADD(r,riv)
      76, // [3][2] - czr: INT_ADD(r,load32)
      77, // [3][3] - czr: INT_ADD(load32,riv)
      280, // [3][4] - czr: INT_MOVE(czr)
      114, // [3][5] - czr: INT_SUB(riv,r)
      117, // [3][6] - czr: INT_SUB(riv,load32)
      118, // [3][7] - czr: INT_SUB(load32,riv)
    },
    { // cz_NT
      0, // [4][0]
      3, // [4][1] - cz: czr
      281, // [4][2] - cz: INT_MOVE(cz)
    },
    { // szpr_NT
      0, // [5][0]
      267, // [5][1] - szpr: INT_2USHORT(r)
      78, // [5][2] - szpr: INT_AND(r,riv)
      80, // [5][3] - szpr: INT_AND(r,load32)
      81, // [5][4] - szpr: INT_AND(load32,riv)
      282, // [5][5] - szpr: INT_MOVE(szpr)
      291, // [5][6] - szpr: INT_NEG(r)
      105, // [5][7] - szpr: INT_OR(r,riv)
      106, // [5][8] - szpr: INT_OR(r,load32)
      107, // [5][9] - szpr: INT_OR(load32,riv)
      541, // [5][10] - szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
      112, // [5][11] - szpr: INT_SHL(riv,riv)
      293, // [5][12] - szpr: INT_SHL(r,INT_CONSTANT)
      345, // [5][13] - szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      542, // [5][14] - szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
      113, // [5][15] - szpr: INT_SHR(riv,riv)
      295, // [5][16] - szpr: INT_SHR(riv,INT_CONSTANT)
      544, // [5][17] - szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
      119, // [5][18] - szpr: INT_USHR(riv,riv)
      296, // [5][19] - szpr: INT_USHR(riv,INT_CONSTANT)
      120, // [5][20] - szpr: INT_XOR(r,riv)
      121, // [5][21] - szpr: INT_XOR(r,load32)
      122, // [5][22] - szpr: INT_XOR(load32,riv)
    },
    { // szp_NT
      0, // [6][0]
      5, // [6][1] - szp: szpr
      79, // [6][2] - szp: INT_AND(r,riv)
      82, // [6][3] - szp: INT_AND(load8_16_32,riv)
      83, // [6][4] - szp: INT_AND(r,load8_16_32)
      283, // [6][5] - szp: INT_MOVE(szp)
    },
    { // riv_NT
      0, // [7][0]
      6, // [7][1] - riv: r
      20, // [7][2] - riv: INT_CONSTANT
    },
    { // rlv_NT
      0, // [8][0]
      7, // [8][1] - rlv: r
      21, // [8][2] - rlv: LONG_CONSTANT
    },
    { // any_NT
      0, // [9][0]
      22, // [9][1] - any: NULL
      8, // [9][2] - any: riv
      23, // [9][3] - any: ADDRESS_CONSTANT
      24, // [9][4] - any: LONG_CONSTANT
      53, // [9][5] - any: OTHER_OPERAND(any,any)
    },
    { // load32_NT
      0, // [10][0]
      290, // [10][1] - load32: INT_MOVE(load32)
      143, // [10][2] - load32: INT_LOAD(riv,riv)
      144, // [10][3] - load32: INT_ALOAD(riv,riv)
      301, // [10][4] - load32: LONG_2INT(load64)
      350, // [10][5] - load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      351, // [10][6] - load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      327, // [10][7] - load32: FLOAT_AS_INT_BITS(float_load)
    },
    { // uload8_NT
      0, // [11][0]
      222, // [11][1] - uload8: INT_AND(load8_16_32,INT_CONSTANT)
      285, // [11][2] - uload8: INT_MOVE(uload8)
      132, // [11][3] - uload8: UBYTE_LOAD(riv,riv)
      134, // [11][4] - uload8: UBYTE_ALOAD(riv,riv)
    },
    { // load8_16_32_NT
      0, // [12][0]
      17, // [12][1] - load8_16_32: load16_32
      18, // [12][2] - load8_16_32: load8
    },
    { // load16_32_NT
      0, // [13][0]
      15, // [13][1] - load16_32: load16
      16, // [13][2] - load16_32: load32
    },
    { // load16_NT
      0, // [14][0]
      289, // [14][1] - load16: INT_MOVE(load16)
      13, // [14][2] - load16: sload16
      14, // [14][3] - load16: uload16
    },
    { // address_NT
      0, // [15][0]
      9, // [15][1] - address: address1scaledreg
      228, // [15][2] - address: INT_MOVE(address)
      61, // [15][3] - address: INT_ADD(r,r)
      62, // [15][4] - address: INT_ADD(r,address1scaledreg)
      63, // [15][5] - address: INT_ADD(address1scaledreg,r)
      229, // [15][6] - address: INT_ADD(address1scaledreg,INT_CONSTANT)
      64, // [15][7] - address: INT_ADD(address1scaledreg,address1reg)
      65, // [15][8] - address: INT_ADD(address1reg,address1scaledreg)
    },
    { // address1scaledreg_NT
      0, // [16][0]
      10, // [16][1] - address1scaledreg: address1reg
      234, // [16][2] - address1scaledreg: INT_MOVE(address1scaledreg)
      235, // [16][3] - address1scaledreg: INT_SHL(r,INT_CONSTANT)
      236, // [16][4] - address1scaledreg: INT_ADD(address1scaledreg,INT_CONSTANT)
    },
    { // address1reg_NT
      0, // [17][0]
      230, // [17][1] - address1reg: INT_ADD(r,INT_CONSTANT)
      231, // [17][2] - address1reg: INT_MOVE(r)
      232, // [17][3] - address1reg: INT_MOVE(address1reg)
      233, // [17][4] - address1reg: INT_ADD(address1reg,INT_CONSTANT)
    },
    { // bittest_NT
      0, // [18][0]
      453, // [18][1] - bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      454, // [18][2] - bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      339, // [18][3] - bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
      455, // [18][4] - bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      456, // [18][5] - bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      340, // [18][6] - bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      457, // [18][7] - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
      458, // [18][8] - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
      459, // [18][9] - bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      460, // [18][10] - bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
    },
    { // boolcmp_NT
      0, // [19][0]
      67, // [19][1] - boolcmp: BOOLEAN_CMP_INT(r,riv)
      240, // [19][2] - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      246, // [19][3] - boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      248, // [19][4] - boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      250, // [19][5] - boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      252, // [19][6] - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      254, // [19][7] - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      69, // [19][8] - boolcmp: BOOLEAN_CMP_INT(load32,riv)
      71, // [19][9] - boolcmp: BOOLEAN_CMP_INT(riv,load32)
      73, // [19][10] - boolcmp: BOOLEAN_CMP_LONG(rlv,rlv)
    },
    { // load8_NT
      0, // [20][0]
      286, // [20][1] - load8: INT_MOVE(load8)
      11, // [20][2] - load8: sload8
      12, // [20][3] - load8: uload8
    },
    { // sload16_NT
      0, // [21][0]
      266, // [21][1] - sload16: INT_2SHORT(load16_32)
      287, // [21][2] - sload16: INT_MOVE(sload16)
      136, // [21][3] - sload16: SHORT_LOAD(riv,riv)
      138, // [21][4] - sload16: SHORT_ALOAD(riv,riv)
    },
    { // load64_NT
      0, // [22][0]
      145, // [22][1] - load64: LONG_LOAD(riv,riv)
      146, // [22][2] - load64: LONG_ALOAD(riv,riv)
      303, // [22][3] - load64: LONG_MOVE(load64)
      329, // [22][4] - load64: DOUBLE_AS_LONG_BITS(double_load)
    },
    { // uload16_NT
      0, // [23][0]
      268, // [23][1] - uload16: INT_2USHORT(load16_32)
      288, // [23][2] - uload16: INT_MOVE(uload16)
      140, // [23][3] - uload16: USHORT_LOAD(riv,riv)
      142, // [23][4] - uload16: USHORT_ALOAD(riv,riv)
    },
    { // sload8_NT
      0, // [24][0]
      284, // [24][1] - sload8: INT_MOVE(sload8)
      128, // [24][2] - sload8: BYTE_LOAD(riv,riv)
      130, // [24][3] - sload8: BYTE_ALOAD(riv,riv)
    },
    { // float_load_NT
      0, // [25][0]
      204, // [25][1] - float_load: FLOAT_LOAD(riv,riv)
      205, // [25][2] - float_load: FLOAT_ALOAD(rlv,riv)
      210, // [25][3] - float_load: FLOAT_ALOAD(riv,riv)
      331, // [25][4] - float_load: INT_BITS_AS_FLOAT(load32)
      335, // [25][5] - float_load: MATERIALIZE_FP_CONSTANT(any)
    },
    { // double_load_NT
      0, // [26][0]
      194, // [26][1] - double_load: DOUBLE_LOAD(riv,riv)
      197, // [26][2] - double_load: DOUBLE_LOAD(rlv,rlv)
      200, // [26][3] - double_load: DOUBLE_ALOAD(rlv,riv)
      201, // [26][4] - double_load: DOUBLE_ALOAD(riv,riv)
      333, // [26][5] - double_load: LONG_BITS_AS_DOUBLE(load64)
      336, // [26][6] - double_load: MATERIALIZE_FP_CONSTANT(any)
    },
  };

  /**
   * Create closure for r
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_r(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 7, c + 0, p.getCost(8) /* rlv */);
    if (c < p.getCost(8) /* rlv */) {
      p.setCost(8 /* rlv */, (char)(c));
      p.writePacked(1, 0xFFFFFFFC, 0x1); // p.rlv = 1
    }
    if(BURS.DEBUG) trace(p, 6, c + 0, p.getCost(7) /* riv */);
    if (c < p.getCost(7) /* riv */) {
      p.setCost(7 /* riv */, (char)(c));
      p.writePacked(0, 0x9FFFFFFF, 0x20000000); // p.riv = 1
      closure_riv(p, c);
    }
    if(BURS.DEBUG) trace(p, 1, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x1); // p.stm = 1
    }
  }

  /**
   * Create closure for czr
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_czr(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 3, c + 0, p.getCost(4) /* cz */);
    if (c < p.getCost(4) /* cz */) {
      p.setCost(4 /* cz */, (char)(c));
      p.writePacked(0, 0xFFE7FFFF, 0x80000); // p.cz = 1
    }
    if(BURS.DEBUG) trace(p, 2, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x200); // p.r = 2
      closure_r(p, c);
    }
  }

  /**
   * Create closure for szpr
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_szpr(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 5, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(0, 0xE3FFFFFF, 0x4000000); // p.szp = 1
    }
    if(BURS.DEBUG) trace(p, 4, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x300); // p.r = 3
      closure_r(p, c);
    }
  }

  /**
   * Create closure for riv
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_riv(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 8, c + 0, p.getCost(9) /* any */);
    if (c < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(c));
      p.writePacked(1, 0xFFFFFFE3, 0x8); // p.any = 2
    }
  }

  /**
   * Create closure for load32
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_load32(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 16, c + 0, p.getCost(13) /* load16_32 */);
    if (c < p.getCost(13) /* load16_32 */) {
      p.setCost(13 /* load16_32 */, (char)(c));
      p.writePacked(1, 0xFFFF9FFF, 0x4000); // p.load16_32 = 2
      closure_load16_32(p, c);
    }
  }

  /**
   * Create closure for uload8
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_uload8(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 12, c + 0, p.getCost(20) /* load8 */);
    if (c < p.getCost(20) /* load8 */) {
      p.setCost(20 /* load8 */, (char)(c));
      p.writePacked(2, 0xFFFFFFCF, 0x30); // p.load8 = 3
      closure_load8(p, c);
    }
  }

  /**
   * Create closure for load16_32
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_load16_32(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 17, c + 0, p.getCost(12) /* load8_16_32 */);
    if (c < p.getCost(12) /* load8_16_32 */) {
      p.setCost(12 /* load8_16_32 */, (char)(c));
      p.writePacked(1, 0xFFFFE7FF, 0x800); // p.load8_16_32 = 1
    }
  }

  /**
   * Create closure for load16
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_load16(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 15, c + 0, p.getCost(13) /* load16_32 */);
    if (c < p.getCost(13) /* load16_32 */) {
      p.setCost(13 /* load16_32 */, (char)(c));
      p.writePacked(1, 0xFFFF9FFF, 0x2000); // p.load16_32 = 1
      closure_load16_32(p, c);
    }
  }

  /**
   * Create closure for address1scaledreg
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_address1scaledreg(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 9, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0x20000); // p.address = 1
    }
  }

  /**
   * Create closure for address1reg
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_address1reg(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 10, c + 0, p.getCost(16) /* address1scaledreg */);
    if (c < p.getCost(16) /* address1scaledreg */) {
      p.setCost(16 /* address1scaledreg */, (char)(c));
      p.writePacked(1, 0xFF1FFFFF, 0x200000); // p.address1scaledreg = 1
      closure_address1scaledreg(p, c);
    }
  }

  /**
   * Create closure for load8
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_load8(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 18, c + 0, p.getCost(12) /* load8_16_32 */);
    if (c < p.getCost(12) /* load8_16_32 */) {
      p.setCost(12 /* load8_16_32 */, (char)(c));
      p.writePacked(1, 0xFFFFE7FF, 0x1000); // p.load8_16_32 = 2
    }
  }

  /**
   * Create closure for sload16
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_sload16(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 13, c + 0, p.getCost(14) /* load16 */);
    if (c < p.getCost(14) /* load16 */) {
      p.setCost(14 /* load16 */, (char)(c));
      p.writePacked(1, 0xFFFE7FFF, 0x10000); // p.load16 = 2
      closure_load16(p, c);
    }
  }

  /**
   * Create closure for uload16
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_uload16(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 14, c + 0, p.getCost(14) /* load16 */);
    if (c < p.getCost(14) /* load16 */) {
      p.setCost(14 /* load16 */, (char)(c));
      p.writePacked(1, 0xFFFE7FFF, 0x18000); // p.load16 = 3
      closure_load16(p, c);
    }
  }

  /**
   * Create closure for sload8
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_sload8(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 11, c + 0, p.getCost(20) /* load8 */);
    if (c < p.getCost(20) /* load8 */) {
      p.setCost(20 /* load8 */, (char)(c));
      p.writePacked(2, 0xFFFFFFCF, 0x20); // p.load8 = 2
      closure_load8(p, c);
    }
  }

  /**
  /** Recursively labels the tree/
   * @param p node to label
   */
  public static void label(AbstractBURS_TreeNode p) {
    switch (p.getOpcode()) {
    case GET_CAUGHT_EXCEPTION_opcode:
      label_GET_CAUGHT_EXCEPTION(p);
      break;
    case SET_CAUGHT_EXCEPTION_opcode:
      label_SET_CAUGHT_EXCEPTION(p);
      break;
    case IG_PATCH_POINT_opcode:
      label_IG_PATCH_POINT(p);
      break;
    case INT_ALOAD_opcode:
      label_INT_ALOAD(p);
      break;
    case LONG_ALOAD_opcode:
      label_LONG_ALOAD(p);
      break;
    case FLOAT_ALOAD_opcode:
      label_FLOAT_ALOAD(p);
      break;
    case DOUBLE_ALOAD_opcode:
      label_DOUBLE_ALOAD(p);
      break;
    case UBYTE_ALOAD_opcode:
      label_UBYTE_ALOAD(p);
      break;
    case BYTE_ALOAD_opcode:
      label_BYTE_ALOAD(p);
      break;
    case USHORT_ALOAD_opcode:
      label_USHORT_ALOAD(p);
      break;
    case SHORT_ALOAD_opcode:
      label_SHORT_ALOAD(p);
      break;
    case INT_ASTORE_opcode:
      label_INT_ASTORE(p);
      break;
    case LONG_ASTORE_opcode:
      label_LONG_ASTORE(p);
      break;
    case FLOAT_ASTORE_opcode:
      label_FLOAT_ASTORE(p);
      break;
    case DOUBLE_ASTORE_opcode:
      label_DOUBLE_ASTORE(p);
      break;
    case BYTE_ASTORE_opcode:
      label_BYTE_ASTORE(p);
      break;
    case SHORT_ASTORE_opcode:
      label_SHORT_ASTORE(p);
      break;
    case INT_IFCMP_opcode:
      label_INT_IFCMP(p);
      break;
    case INT_IFCMP2_opcode:
      label_INT_IFCMP2(p);
      break;
    case LONG_IFCMP_opcode:
      label_LONG_IFCMP(p);
      break;
    case FLOAT_IFCMP_opcode:
      label_FLOAT_IFCMP(p);
      break;
    case DOUBLE_IFCMP_opcode:
      label_DOUBLE_IFCMP(p);
      break;
    case UNINT_BEGIN_opcode:
      label_UNINT_BEGIN(p);
      break;
    case UNINT_END_opcode:
      label_UNINT_END(p);
      break;
    case FENCE_opcode:
      label_FENCE(p);
      break;
    case READ_CEILING_opcode:
      label_READ_CEILING(p);
      break;
    case WRITE_FLOOR_opcode:
      label_WRITE_FLOOR(p);
      break;
    case NOP_opcode:
      label_NOP(p);
      break;
    case INT_MOVE_opcode:
      label_INT_MOVE(p);
      break;
    case LONG_MOVE_opcode:
      label_LONG_MOVE(p);
      break;
    case FLOAT_MOVE_opcode:
      label_FLOAT_MOVE(p);
      break;
    case DOUBLE_MOVE_opcode:
      label_DOUBLE_MOVE(p);
      break;
    case GUARD_MOVE_opcode:
      label_GUARD_MOVE(p);
      break;
    case GUARD_COMBINE_opcode:
      label_GUARD_COMBINE(p);
      break;
    case INT_ADD_opcode:
      label_INT_ADD(p);
      break;
    case LONG_ADD_opcode:
      label_LONG_ADD(p);
      break;
    case FLOAT_ADD_opcode:
      label_FLOAT_ADD(p);
      break;
    case DOUBLE_ADD_opcode:
      label_DOUBLE_ADD(p);
      break;
    case INT_SUB_opcode:
      label_INT_SUB(p);
      break;
    case LONG_SUB_opcode:
      label_LONG_SUB(p);
      break;
    case FLOAT_SUB_opcode:
      label_FLOAT_SUB(p);
      break;
    case DOUBLE_SUB_opcode:
      label_DOUBLE_SUB(p);
      break;
    case INT_MUL_opcode:
      label_INT_MUL(p);
      break;
    case LONG_MUL_opcode:
      label_LONG_MUL(p);
      break;
    case FLOAT_MUL_opcode:
      label_FLOAT_MUL(p);
      break;
    case DOUBLE_MUL_opcode:
      label_DOUBLE_MUL(p);
      break;
    case INT_DIV_opcode:
      label_INT_DIV(p);
      break;
    case UNSIGNED_DIV_64_32_opcode:
      label_UNSIGNED_DIV_64_32(p);
      break;
    case UNSIGNED_REM_64_32_opcode:
      label_UNSIGNED_REM_64_32(p);
      break;
    case FLOAT_DIV_opcode:
      label_FLOAT_DIV(p);
      break;
    case DOUBLE_DIV_opcode:
      label_DOUBLE_DIV(p);
      break;
    case INT_REM_opcode:
      label_INT_REM(p);
      break;
    case FLOAT_REM_opcode:
      label_FLOAT_REM(p);
      break;
    case DOUBLE_REM_opcode:
      label_DOUBLE_REM(p);
      break;
    case INT_NEG_opcode:
      label_INT_NEG(p);
      break;
    case LONG_NEG_opcode:
      label_LONG_NEG(p);
      break;
    case FLOAT_NEG_opcode:
      label_FLOAT_NEG(p);
      break;
    case DOUBLE_NEG_opcode:
      label_DOUBLE_NEG(p);
      break;
    case FLOAT_SQRT_opcode:
      label_FLOAT_SQRT(p);
      break;
    case DOUBLE_SQRT_opcode:
      label_DOUBLE_SQRT(p);
      break;
    case INT_SHL_opcode:
      label_INT_SHL(p);
      break;
    case LONG_SHL_opcode:
      label_LONG_SHL(p);
      break;
    case INT_SHR_opcode:
      label_INT_SHR(p);
      break;
    case LONG_SHR_opcode:
      label_LONG_SHR(p);
      break;
    case INT_USHR_opcode:
      label_INT_USHR(p);
      break;
    case LONG_USHR_opcode:
      label_LONG_USHR(p);
      break;
    case INT_AND_opcode:
      label_INT_AND(p);
      break;
    case LONG_AND_opcode:
      label_LONG_AND(p);
      break;
    case INT_OR_opcode:
      label_INT_OR(p);
      break;
    case LONG_OR_opcode:
      label_LONG_OR(p);
      break;
    case INT_XOR_opcode:
      label_INT_XOR(p);
      break;
    case INT_NOT_opcode:
      label_INT_NOT(p);
      break;
    case LONG_NOT_opcode:
      label_LONG_NOT(p);
      break;
    case LONG_XOR_opcode:
      label_LONG_XOR(p);
      break;
    case ADDR_2LONG_opcode:
      label_ADDR_2LONG(p);
      break;
    case INT_2LONG_opcode:
      label_INT_2LONG(p);
      break;
    case INT_2FLOAT_opcode:
      label_INT_2FLOAT(p);
      break;
    case INT_2DOUBLE_opcode:
      label_INT_2DOUBLE(p);
      break;
    case LONG_2INT_opcode:
      label_LONG_2INT(p);
      break;
    case LONG_2FLOAT_opcode:
      label_LONG_2FLOAT(p);
      break;
    case LONG_2DOUBLE_opcode:
      label_LONG_2DOUBLE(p);
      break;
    case FLOAT_2INT_opcode:
      label_FLOAT_2INT(p);
      break;
    case FLOAT_2LONG_opcode:
      label_FLOAT_2LONG(p);
      break;
    case FLOAT_2DOUBLE_opcode:
      label_FLOAT_2DOUBLE(p);
      break;
    case DOUBLE_2INT_opcode:
      label_DOUBLE_2INT(p);
      break;
    case DOUBLE_2LONG_opcode:
      label_DOUBLE_2LONG(p);
      break;
    case DOUBLE_2FLOAT_opcode:
      label_DOUBLE_2FLOAT(p);
      break;
    case INT_2BYTE_opcode:
      label_INT_2BYTE(p);
      break;
    case INT_2USHORT_opcode:
      label_INT_2USHORT(p);
      break;
    case INT_2SHORT_opcode:
      label_INT_2SHORT(p);
      break;
    case LONG_CMP_opcode:
      label_LONG_CMP(p);
      break;
    case RETURN_opcode:
      label_RETURN(p);
      break;
    case NULL_CHECK_opcode:
      label_NULL_CHECK(p);
      break;
    case GOTO_opcode:
      label_GOTO(p);
      break;
    case BOOLEAN_NOT_opcode:
      label_BOOLEAN_NOT(p);
      break;
    case BOOLEAN_CMP_INT_opcode:
      label_BOOLEAN_CMP_INT(p);
      break;
    case BOOLEAN_CMP_LONG_opcode:
      label_BOOLEAN_CMP_LONG(p);
      break;
    case BYTE_LOAD_opcode:
      label_BYTE_LOAD(p);
      break;
    case UBYTE_LOAD_opcode:
      label_UBYTE_LOAD(p);
      break;
    case SHORT_LOAD_opcode:
      label_SHORT_LOAD(p);
      break;
    case USHORT_LOAD_opcode:
      label_USHORT_LOAD(p);
      break;
    case INT_LOAD_opcode:
      label_INT_LOAD(p);
      break;
    case LONG_LOAD_opcode:
      label_LONG_LOAD(p);
      break;
    case FLOAT_LOAD_opcode:
      label_FLOAT_LOAD(p);
      break;
    case DOUBLE_LOAD_opcode:
      label_DOUBLE_LOAD(p);
      break;
    case BYTE_STORE_opcode:
      label_BYTE_STORE(p);
      break;
    case SHORT_STORE_opcode:
      label_SHORT_STORE(p);
      break;
    case INT_STORE_opcode:
      label_INT_STORE(p);
      break;
    case LONG_STORE_opcode:
      label_LONG_STORE(p);
      break;
    case FLOAT_STORE_opcode:
      label_FLOAT_STORE(p);
      break;
    case DOUBLE_STORE_opcode:
      label_DOUBLE_STORE(p);
      break;
    case ATTEMPT_INT_opcode:
      label_ATTEMPT_INT(p);
      break;
    case ATTEMPT_LONG_opcode:
      label_ATTEMPT_LONG(p);
      break;
    case CALL_opcode:
      label_CALL(p);
      break;
    case SYSCALL_opcode:
      label_SYSCALL(p);
      break;
    case YIELDPOINT_PROLOGUE_opcode:
      label_YIELDPOINT_PROLOGUE(p);
      break;
    case YIELDPOINT_EPILOGUE_opcode:
      label_YIELDPOINT_EPILOGUE(p);
      break;
    case YIELDPOINT_BACKEDGE_opcode:
      label_YIELDPOINT_BACKEDGE(p);
      break;
    case YIELDPOINT_OSR_opcode:
      label_YIELDPOINT_OSR(p);
      break;
    case IR_PROLOGUE_opcode:
      label_IR_PROLOGUE(p);
      break;
    case RESOLVE_opcode:
      label_RESOLVE(p);
      break;
    case GET_TIME_BASE_opcode:
      label_GET_TIME_BASE(p);
      break;
    case TRAP_IF_opcode:
      label_TRAP_IF(p);
      break;
    case TRAP_opcode:
      label_TRAP(p);
      break;
    case ILLEGAL_INSTRUCTION_opcode:
      label_ILLEGAL_INSTRUCTION(p);
      break;
    case FLOAT_AS_INT_BITS_opcode:
      label_FLOAT_AS_INT_BITS(p);
      break;
    case INT_BITS_AS_FLOAT_opcode:
      label_INT_BITS_AS_FLOAT(p);
      break;
    case DOUBLE_AS_LONG_BITS_opcode:
      label_DOUBLE_AS_LONG_BITS(p);
      break;
    case LONG_BITS_AS_DOUBLE_opcode:
      label_LONG_BITS_AS_DOUBLE(p);
      break;
    case FRAMESIZE_opcode:
      label_FRAMESIZE(p);
      break;
    case LOWTABLESWITCH_opcode:
      label_LOWTABLESWITCH(p);
      break;
    case ADDRESS_CONSTANT_opcode:
      label_ADDRESS_CONSTANT(p);
      break;
    case INT_CONSTANT_opcode:
      label_INT_CONSTANT(p);
      break;
    case LONG_CONSTANT_opcode:
      label_LONG_CONSTANT(p);
      break;
    case REGISTER_opcode:
      label_REGISTER(p);
      break;
    case OTHER_OPERAND_opcode:
      label_OTHER_OPERAND(p);
      break;
    case NULL_opcode:
      label_NULL(p);
      break;
    case BRANCH_TARGET_opcode:
      label_BRANCH_TARGET(p);
      break;
    case MATERIALIZE_FP_CONSTANT_opcode:
      label_MATERIALIZE_FP_CONSTANT(p);
      break;
    case CLEAR_FLOATING_POINT_STATE_opcode:
      label_CLEAR_FLOATING_POINT_STATE(p);
      break;
    case PREFETCH_opcode:
      label_PREFETCH(p);
      break;
    case PAUSE_opcode:
      label_PAUSE(p);
      break;
    case CMP_CMOV_opcode:
      label_CMP_CMOV(p);
      break;
    case FCMP_CMOV_opcode:
      label_FCMP_CMOV(p);
      break;
    case LCMP_CMOV_opcode:
      label_LCMP_CMOV(p);
      break;
    case FCMP_FCMOV_opcode:
      label_FCMP_FCMOV(p);
      break;
    default:
      throw new OptimizingCompilerException("BURS","terminal not in grammar:",
        p.toString());
    }
  }

  /**
   * Labels GET_CAUGHT_EXCEPTION tree node
   * @param p node to label
   */
  private static void label_GET_CAUGHT_EXCEPTION(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: GET_CAUGHT_EXCEPTION
    if(BURS.DEBUG) trace(p, 37, 11 + 0, p.getCost(2) /* r */);
    if (11 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(11));
      p.writePacked(0, 0xFFFF00FF, 0x700); // p.r = 7
      closure_r(p, 11);
    }
  }

  /**
   * Labels SET_CAUGHT_EXCEPTION tree node
   * @param p node to label
   */
  private static void label_SET_CAUGHT_EXCEPTION(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // stm: SET_CAUGHT_EXCEPTION(r)
    c = STATE(lchild).getCost(2 /* r */) + 11;
    if(BURS.DEBUG) trace(p, 219, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xD); // p.stm = 13
    }
    if ( // stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = 20;
      if(BURS.DEBUG) trace(p, 38, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xE); // p.stm = 14
      }
    }
    if ( // stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
      lchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = 20;
      if(BURS.DEBUG) trace(p, 39, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xF); // p.stm = 15
      }
    }
  }

  /**
   * Labels IG_PATCH_POINT tree node
   * @param p node to label
   */
  private static void label_IG_PATCH_POINT(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: IG_PATCH_POINT
    if(BURS.DEBUG) trace(p, 25, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x2); // p.stm = 2
    }
  }

  /**
   * Labels INT_ALOAD tree node
   * @param p node to label
   */
  private static void label_INT_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: INT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 101, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5900); // p.r = 89
      closure_r(p, c);
    }
    // load32: INT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 144, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFFF1F, 0x60); // p.load32 = 3
      closure_load32(p, c);
    }
  }

  /**
   * Labels LONG_ALOAD tree node
   * @param p node to label
   */
  private static void label_LONG_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // load64: LONG_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 146, c + 0, p.getCost(22) /* load64 */);
    if (c < p.getCost(22) /* load64 */) {
      p.setCost(22 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFFF1FF, 0x400); // p.load64 = 2
    }
    // r: LONG_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 30;
    if(BURS.DEBUG) trace(p, 155, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8A00); // p.r = 138
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_ALOAD tree node
   * @param p node to label
   */
  private static void label_FLOAT_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // float_load: FLOAT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 205, c + 0, p.getCost(25) /* float_load */);
    if (c < p.getCost(25) /* float_load */) {
      p.setCost(25 /* float_load */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x40000); // p.float_load = 2
    }
    // r: FLOAT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 206, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC900); // p.r = 201
      closure_r(p, c);
    }
    // r: FLOAT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 207, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xCA00); // p.r = 202
      closure_r(p, c);
    }
    // r: FLOAT_ALOAD(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 208, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xCB00); // p.r = 203
      closure_r(p, c);
    }
    // r: FLOAT_ALOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 209, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xCC00); // p.r = 204
      closure_r(p, c);
    }
    // float_load: FLOAT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 210, c + 0, p.getCost(25) /* float_load */);
    if (c < p.getCost(25) /* float_load */) {
      p.setCost(25 /* float_load */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x60000); // p.float_load = 3
    }
  }

  /**
   * Labels DOUBLE_ALOAD tree node
   * @param p node to label
   */
  private static void label_DOUBLE_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 195, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC300); // p.r = 195
      closure_r(p, c);
    }
    // r: DOUBLE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 196, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC400); // p.r = 196
      closure_r(p, c);
    }
    // r: DOUBLE_ALOAD(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 198, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC500); // p.r = 197
      closure_r(p, c);
    }
    // r: DOUBLE_ALOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 10;
    if(BURS.DEBUG) trace(p, 199, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC600); // p.r = 198
      closure_r(p, c);
    }
    // double_load: DOUBLE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 200, c + 0, p.getCost(26) /* double_load */);
    if (c < p.getCost(26) /* double_load */) {
      p.setCost(26 /* double_load */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x300000); // p.double_load = 3
    }
    // double_load: DOUBLE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 201, c + 0, p.getCost(26) /* double_load */);
    if (c < p.getCost(26) /* double_load */) {
      p.setCost(26 /* double_load */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x400000); // p.double_load = 4
    }
  }

  /**
   * Labels UBYTE_ALOAD tree node
   * @param p node to label
   */
  private static void label_UBYTE_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: UBYTE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 133, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7800); // p.r = 120
      closure_r(p, c);
    }
    // uload8: UBYTE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 134, c + 0, p.getCost(11) /* uload8 */);
    if (c < p.getCost(11) /* uload8 */) {
      p.setCost(11 /* uload8 */, (char)(c));
      p.writePacked(1, 0xFFFFF8FF, 0x400); // p.uload8 = 4
      closure_uload8(p, c);
    }
  }

  /**
   * Labels BYTE_ALOAD tree node
   * @param p node to label
   */
  private static void label_BYTE_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: BYTE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 129, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7600); // p.r = 118
      closure_r(p, c);
    }
    // sload8: BYTE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 130, c + 0, p.getCost(24) /* sload8 */);
    if (c < p.getCost(24) /* sload8 */) {
      p.setCost(24 /* sload8 */, (char)(c));
      p.writePacked(2, 0xFFFE7FFF, 0x18000); // p.sload8 = 3
      closure_sload8(p, c);
    }
  }

  /**
   * Labels USHORT_ALOAD tree node
   * @param p node to label
   */
  private static void label_USHORT_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: USHORT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 141, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7C00); // p.r = 124
      closure_r(p, c);
    }
    // uload16: USHORT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 142, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x4000); // p.uload16 = 4
      closure_uload16(p, c);
    }
  }

  /**
   * Labels SHORT_ALOAD tree node
   * @param p node to label
   */
  private static void label_SHORT_ALOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: SHORT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 137, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7A00); // p.r = 122
      closure_r(p, c);
    }
    // sload16: SHORT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 138, c + 0, p.getCost(21) /* sload16 */);
    if (c < p.getCost(21) /* sload16 */) {
      p.setCost(21 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFFFFE3F, 0x100); // p.sload16 = 4
      closure_sload16(p, c);
    }
  }

  /**
   * Labels INT_ASTORE tree node
   * @param p node to label
   */
  private static void label_INT_ASTORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 360, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1D); // p.stm = 29
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 361, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1E); // p.stm = 30
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 362, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1F); // p.stm = 31
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 363, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x20); // p.stm = 32
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 364, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x21); // p.stm = 33
      }
    }
    if ( // stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_ADD_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 494, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x51); // p.stm = 81
      }
    }
    if ( // stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_ADD_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 514, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x52); // p.stm = 82
      }
    }
    if ( // stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 496, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x55); // p.stm = 85
      }
    }
    if ( // stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 516, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x56); // p.stm = 86
      }
    }
    if ( // stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NEG_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 464, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x68); // p.stm = 104
      }
    }
    if ( // stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NOT_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 466, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6A); // p.stm = 106
      }
    }
    if ( // stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 498, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6D); // p.stm = 109
      }
    }
    if ( // stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 518, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6E); // p.stm = 110
      }
    }
    if ( // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 31 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 549, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x71); // p.stm = 113
      }
    }
    if ( // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 31 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 468, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x72); // p.stm = 114
      }
    }
    if ( // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 31 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 551, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x75); // p.stm = 117
      }
    }
    if ( // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 31 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 470, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x76); // p.stm = 118
      }
    }
    if ( // stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 500, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7F); // p.stm = 127
      }
    }
    if ( // stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 27);
      if(BURS.DEBUG) trace(p, 520, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x80); // p.stm = 128
      }
    }
    if ( // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 31 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 553, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x83); // p.stm = 131
      }
    }
    if ( // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 31 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 472, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x84); // p.stm = 132
      }
    }
    if ( // stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 502, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x87); // p.stm = 135
      }
    }
    if ( // stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 522, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x88); // p.stm = 136
      }
    }
    if ( // stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_2INT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 492, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8A); // p.stm = 138
      }
    }
  }

  /**
   * Labels LONG_ASTORE tree node
   * @param p node to label
   */
  private static void label_LONG_ASTORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 30;
      if(BURS.DEBUG) trace(p, 365, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x22); // p.stm = 34
      }
    }
    if ( // stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 366, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x23); // p.stm = 35
      }
    }
    if ( // stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 367, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x24); // p.stm = 36
      }
    }
    if ( // stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 26;
      if(BURS.DEBUG) trace(p, 416, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x25); // p.stm = 37
      }
    }
    if ( // stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
      lchild.getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 26;
      if(BURS.DEBUG) trace(p, 417, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x26); // p.stm = 38
      }
    }
    if ( // stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_ADD_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 504, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8D); // p.stm = 141
      }
    }
    if ( // stm: LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_ADD_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 524, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8E); // p.stm = 142
      }
    }
    if ( // stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 506, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x91); // p.stm = 145
      }
    }
    if ( // stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 526, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x92); // p.stm = 146
      }
    }
    if ( // stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NEG_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 474, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x95); // p.stm = 149
      }
    }
    if ( // stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NOT_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 476, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x97); // p.stm = 151
      }
    }
    if ( // stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 508, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9A); // p.stm = 154
      }
    }
    if ( // stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 528, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9B); // p.stm = 155
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_SUB_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 510, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9F); // p.stm = 159
      }
    }
    if ( // stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 512, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA2); // p.stm = 162
      }
    }
    if ( // stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 530, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA3); // p.stm = 163
      }
    }
    if ( // stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 412, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBD); // p.stm = 189
      }
    }
    if ( // stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 413, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBE); // p.stm = 190
      }
    }
  }

  /**
   * Labels FLOAT_ASTORE tree node
   * @param p node to label
   */
  private static void label_FLOAT_ASTORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 399, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB1); // p.stm = 177
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 400, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB2); // p.stm = 178
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 401, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB3); // p.stm = 179
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 402, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB4); // p.stm = 180
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 12;
      if(BURS.DEBUG) trace(p, 403, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB5); // p.stm = 181
      }
    }
  }

  /**
   * Labels DOUBLE_ASTORE tree node
   * @param p node to label
   */
  private static void label_DOUBLE_ASTORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 390, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA8); // p.stm = 168
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 391, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA9); // p.stm = 169
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 392, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAA); // p.stm = 170
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 393, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAB); // p.stm = 171
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 12;
      if(BURS.DEBUG) trace(p, 394, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAC); // p.stm = 172
      }
    }
  }

  /**
   * Labels BYTE_ASTORE tree node
   * @param p node to label
   */
  private static void label_BYTE_ASTORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 369, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x42); // p.stm = 66
      }
    }
    if ( // stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == BOOLEAN_NOT_opcode && 
      lchild.getChild1().getOpcode() == UBYTE_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 462, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x44); // p.stm = 68
      }
    }
    if ( // stm: BYTE_ASTORE(riv,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 372, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x47); // p.stm = 71
      }
    }
    if ( // stm: BYTE_ASTORE(load8,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load8 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 373, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x48); // p.stm = 72
      }
    }
    if ( // stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2BYTE_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 486, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4A); // p.stm = 74
      }
    }
  }

  /**
   * Labels SHORT_ASTORE tree node
   * @param p node to label
   */
  private static void label_SHORT_ASTORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 357, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1A); // p.stm = 26
      }
    }
    if ( // stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(14 /* load16 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 358, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1B); // p.stm = 27
      }
    }
    if ( // stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 359, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1C); // p.stm = 28
      }
    }
    if ( // stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2SHORT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 488, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4C); // p.stm = 76
      }
    }
    if ( // stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2USHORT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 490, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4E); // p.stm = 78
      }
    }
  }

  /**
   * Labels INT_IFCMP tree node
   * @param p node to label
   */
  private static void label_INT_IFCMP(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 439, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x33); // p.stm = 51
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 440, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x34); // p.stm = 52
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 441, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x35); // p.stm = 53
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(17 /* address1reg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 442, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x36); // p.stm = 54
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(17 /* address1reg */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 443, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x37); // p.stm = 55
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(15 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 449, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x38); // p.stm = 56
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(15 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 451, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x39); // p.stm = 57
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 444, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x3A); // p.stm = 58
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 445, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x3B); // p.stm = 59
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 446, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x3C); // p.stm = 60
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(17 /* address1reg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 447, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x3D); // p.stm = 61
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(17 /* address1reg */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 448, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x3E); // p.stm = 62
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(15 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 450, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x3F); // p.stm = 63
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_INT_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(15 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 452, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x40); // p.stm = 64
      }
    }
    // stm: INT_IFCMP(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 26;
    if(BURS.DEBUG) trace(p, 88, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x57); // p.stm = 87
    }
    if ( // stm: INT_IFCMP(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && CMP_TO_TEST(IfCmp.getCond(P(p))) ? 24:INFINITE);
      if(BURS.DEBUG) trace(p, 270, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x58); // p.stm = 88
      }
    }
    if ( // stm: INT_IFCMP(load8,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load8 */) + FITS(IfCmp.getVal2(P(p)), 8, 28);
      if(BURS.DEBUG) trace(p, 271, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x59); // p.stm = 89
      }
    }
    // stm: INT_IFCMP(uload8,r)
    c = STATE(lchild).getCost(11 /* uload8 */) + STATE(rchild).getCost(2 /* r */) + 28;
    if(BURS.DEBUG) trace(p, 89, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x5A); // p.stm = 90
    }
    // stm: INT_IFCMP(r,uload8)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(11 /* uload8 */) + 28;
    if(BURS.DEBUG) trace(p, 90, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x5B); // p.stm = 91
    }
    if ( // stm: INT_IFCMP(sload16,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(21 /* sload16 */) + FITS(IfCmp.getVal2(P(p)), 8, 28);
      if(BURS.DEBUG) trace(p, 272, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5C); // p.stm = 92
      }
    }
    // stm: INT_IFCMP(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 28;
    if(BURS.DEBUG) trace(p, 91, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x5D); // p.stm = 93
    }
    // stm: INT_IFCMP(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 28;
    if(BURS.DEBUG) trace(p, 92, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x5E); // p.stm = 94
    }
    if ( // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && IfCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 1 && IfCmp.getCond(P(p)).isEQUAL()) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 273, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5F); // p.stm = 95
      }
    }
    if ( // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && IfCmp.getCond(P(p)).isEQUAL()) || (VR(p) == 1 && IfCmp.getCond(P(p)).isNOT_EQUAL()) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 274, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x60); // p.stm = 96
      }
    }
    if ( // stm: INT_IFCMP(cz,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + isZERO(VR(p), 11);
      if(BURS.DEBUG) trace(p, 275, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x61); // p.stm = 97
      }
    }
    if ( // stm: INT_IFCMP(szp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + (VR(p) == 0 && EQ_NE(IfCmp.getCond(P(p)))?11:INFINITE);
      if(BURS.DEBUG) trace(p, 276, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x62); // p.stm = 98
      }
    }
    if ( // stm: INT_IFCMP(bittest,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + ((VR(p) == 0 || VR(p) == 1) && EQ_NE(IfCmp.getCond(P(p))) ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 277, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x63); // p.stm = 99
      }
    }
  }

  /**
   * Labels INT_IFCMP2 tree node
   * @param p node to label
   */
  private static void label_INT_IFCMP2(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // stm: INT_IFCMP2(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 26;
    if(BURS.DEBUG) trace(p, 93, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x64); // p.stm = 100
    }
    // stm: INT_IFCMP2(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 28;
    if(BURS.DEBUG) trace(p, 94, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x65); // p.stm = 101
    }
    // stm: INT_IFCMP2(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 28;
    if(BURS.DEBUG) trace(p, 95, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x66); // p.stm = 102
    }
  }

  /**
   * Labels LONG_IFCMP tree node
   * @param p node to label
   */
  private static void label_LONG_IFCMP(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // stm: LONG_IFCMP(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 30;
    if(BURS.DEBUG) trace(p, 153, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x93); // p.stm = 147
    }
  }

  /**
   * Labels FLOAT_IFCMP tree node
   * @param p node to label
   */
  private static void label_FLOAT_IFCMP(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // stm: FLOAT_IFCMP(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 211, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xB7); // p.stm = 183
    }
    // stm: FLOAT_IFCMP(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(25 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 212, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xB8); // p.stm = 184
    }
    // stm: FLOAT_IFCMP(float_load,r)
    c = STATE(lchild).getCost(25 /* float_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 213, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xB9); // p.stm = 185
    }
  }

  /**
   * Labels DOUBLE_IFCMP tree node
   * @param p node to label
   */
  private static void label_DOUBLE_IFCMP(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // stm: DOUBLE_IFCMP(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 214, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xBA); // p.stm = 186
    }
    // stm: DOUBLE_IFCMP(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 215, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xBB); // p.stm = 187
    }
    // stm: DOUBLE_IFCMP(double_load,r)
    c = STATE(lchild).getCost(26 /* double_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 216, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xBC); // p.stm = 188
    }
  }

  /**
   * Labels UNINT_BEGIN tree node
   * @param p node to label
   */
  private static void label_UNINT_BEGIN(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: UNINT_BEGIN
    if(BURS.DEBUG) trace(p, 26, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x3); // p.stm = 3
    }
  }

  /**
   * Labels UNINT_END tree node
   * @param p node to label
   */
  private static void label_UNINT_END(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: UNINT_END
    if(BURS.DEBUG) trace(p, 27, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x4); // p.stm = 4
    }
  }

  /**
   * Labels FENCE tree node
   * @param p node to label
   */
  private static void label_FENCE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: FENCE
    if(BURS.DEBUG) trace(p, 44, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0x2B); // p.stm = 43
    }
  }

  /**
   * Labels READ_CEILING tree node
   * @param p node to label
   */
  private static void label_READ_CEILING(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: READ_CEILING
    if(BURS.DEBUG) trace(p, 43, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0x2A); // p.stm = 42
    }
  }

  /**
   * Labels WRITE_FLOOR tree node
   * @param p node to label
   */
  private static void label_WRITE_FLOOR(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: WRITE_FLOOR
    if(BURS.DEBUG) trace(p, 42, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0x29); // p.stm = 41
    }
  }

  /**
   * Labels NOP tree node
   * @param p node to label
   */
  private static void label_NOP(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: NOP
    if(BURS.DEBUG) trace(p, 33, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0xA); // p.stm = 10
    }
  }

  /**
   * Labels INT_MOVE tree node
   * @param p node to label
   */
  private static void label_INT_MOVE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // address: INT_MOVE(address)
    c = STATE(lchild).getCost(15 /* address */) + 0;
    if(BURS.DEBUG) trace(p, 228, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0x40000); // p.address = 2
    }
    // address1reg: INT_MOVE(r)
    c = STATE(lchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 231, c + 0, p.getCost(17) /* address1reg */);
    if (c < p.getCost(17) /* address1reg */) {
      p.setCost(17 /* address1reg */, (char)(c));
      p.writePacked(1, 0xF8FFFFFF, 0x2000000); // p.address1reg = 2
      closure_address1reg(p, c);
    }
    // address1reg: INT_MOVE(address1reg)
    c = STATE(lchild).getCost(17 /* address1reg */) + 0;
    if(BURS.DEBUG) trace(p, 232, c + 0, p.getCost(17) /* address1reg */);
    if (c < p.getCost(17) /* address1reg */) {
      p.setCost(17 /* address1reg */, (char)(c));
      p.writePacked(1, 0xF8FFFFFF, 0x3000000); // p.address1reg = 3
      closure_address1reg(p, c);
    }
    // address1scaledreg: INT_MOVE(address1scaledreg)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 234, c + 0, p.getCost(16) /* address1scaledreg */);
    if (c < p.getCost(16) /* address1scaledreg */) {
      p.setCost(16 /* address1scaledreg */, (char)(c));
      p.writePacked(1, 0xFF1FFFFF, 0x400000); // p.address1scaledreg = 2
      closure_address1scaledreg(p, c);
    }
    // r: INT_MOVE(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 279, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5A00); // p.r = 90
      closure_r(p, c);
    }
    // czr: INT_MOVE(czr)
    c = STATE(lchild).getCost(3 /* czr */) + 11;
    if(BURS.DEBUG) trace(p, 280, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x40000); // p.czr = 4
      closure_czr(p, c);
    }
    // cz: INT_MOVE(cz)
    c = STATE(lchild).getCost(4 /* cz */) + 0;
    if(BURS.DEBUG) trace(p, 281, c + 0, p.getCost(4) /* cz */);
    if (c < p.getCost(4) /* cz */) {
      p.setCost(4 /* cz */, (char)(c));
      p.writePacked(0, 0xFFE7FFFF, 0x100000); // p.cz = 2
    }
    // szpr: INT_MOVE(szpr)
    c = STATE(lchild).getCost(5 /* szpr */) + 11;
    if(BURS.DEBUG) trace(p, 282, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0xA00000); // p.szpr = 5
      closure_szpr(p, c);
    }
    // szp: INT_MOVE(szp)
    c = STATE(lchild).getCost(6 /* szp */) + 0;
    if(BURS.DEBUG) trace(p, 283, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(0, 0xE3FFFFFF, 0x14000000); // p.szp = 5
    }
    // sload8: INT_MOVE(sload8)
    c = STATE(lchild).getCost(24 /* sload8 */) + 0;
    if(BURS.DEBUG) trace(p, 284, c + 0, p.getCost(24) /* sload8 */);
    if (c < p.getCost(24) /* sload8 */) {
      p.setCost(24 /* sload8 */, (char)(c));
      p.writePacked(2, 0xFFFE7FFF, 0x8000); // p.sload8 = 1
      closure_sload8(p, c);
    }
    // uload8: INT_MOVE(uload8)
    c = STATE(lchild).getCost(11 /* uload8 */) + 0;
    if(BURS.DEBUG) trace(p, 285, c + 0, p.getCost(11) /* uload8 */);
    if (c < p.getCost(11) /* uload8 */) {
      p.setCost(11 /* uload8 */, (char)(c));
      p.writePacked(1, 0xFFFFF8FF, 0x200); // p.uload8 = 2
      closure_uload8(p, c);
    }
    // load8: INT_MOVE(load8)
    c = STATE(lchild).getCost(20 /* load8 */) + 0;
    if(BURS.DEBUG) trace(p, 286, c + 0, p.getCost(20) /* load8 */);
    if (c < p.getCost(20) /* load8 */) {
      p.setCost(20 /* load8 */, (char)(c));
      p.writePacked(2, 0xFFFFFFCF, 0x10); // p.load8 = 1
      closure_load8(p, c);
    }
    // sload16: INT_MOVE(sload16)
    c = STATE(lchild).getCost(21 /* sload16 */) + 0;
    if(BURS.DEBUG) trace(p, 287, c + 0, p.getCost(21) /* sload16 */);
    if (c < p.getCost(21) /* sload16 */) {
      p.setCost(21 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFFFFE3F, 0x80); // p.sload16 = 2
      closure_sload16(p, c);
    }
    // uload16: INT_MOVE(uload16)
    c = STATE(lchild).getCost(23 /* uload16 */) + 0;
    if(BURS.DEBUG) trace(p, 288, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x2000); // p.uload16 = 2
      closure_uload16(p, c);
    }
    // load16: INT_MOVE(load16)
    c = STATE(lchild).getCost(14 /* load16 */) + 0;
    if(BURS.DEBUG) trace(p, 289, c + 0, p.getCost(14) /* load16 */);
    if (c < p.getCost(14) /* load16 */) {
      p.setCost(14 /* load16 */, (char)(c));
      p.writePacked(1, 0xFFFE7FFF, 0x8000); // p.load16 = 1
      closure_load16(p, c);
    }
    // load32: INT_MOVE(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 0;
    if(BURS.DEBUG) trace(p, 290, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFFF1F, 0x20); // p.load32 = 1
      closure_load32(p, c);
    }
    // r: INT_MOVE(address)
    c = STATE(lchild).getCost(15 /* address */) + 20;
    if(BURS.DEBUG) trace(p, 298, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7400); // p.r = 116
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_MOVE tree node
   * @param p node to label
   */
  private static void label_LONG_MOVE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_MOVE(r)
    c = STATE(lchild).getCost(2 /* r */) + 23;
    if(BURS.DEBUG) trace(p, 302, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8B00); // p.r = 139
      closure_r(p, c);
    }
    if ( // r: LONG_MOVE(LONG_CONSTANT)
      lchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = 21;
      if(BURS.DEBUG) trace(p, 51, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x8C00); // p.r = 140
        closure_r(p, c);
      }
    }
    // load64: LONG_MOVE(load64)
    c = STATE(lchild).getCost(22 /* load64 */) + 0;
    if(BURS.DEBUG) trace(p, 303, c + 0, p.getCost(22) /* load64 */);
    if (c < p.getCost(22) /* load64 */) {
      p.setCost(22 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFFF1FF, 0x600); // p.load64 = 3
    }
  }

  /**
   * Labels FLOAT_MOVE tree node
   * @param p node to label
   */
  private static void label_FLOAT_MOVE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_MOVE(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 312, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xBE00); // p.r = 190
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_MOVE tree node
   * @param p node to label
   */
  private static void label_DOUBLE_MOVE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_MOVE(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 313, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xBF00); // p.r = 191
      closure_r(p, c);
    }
  }

  /**
   * Labels GUARD_MOVE tree node
   * @param p node to label
   */
  private static void label_GUARD_MOVE(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: GUARD_MOVE
    if(BURS.DEBUG) trace(p, 34, 11 + 0, p.getCost(2) /* r */);
    if (11 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(11));
      p.writePacked(0, 0xFFFF00FF, 0x500); // p.r = 5
      closure_r(p, 11);
    }
  }

  /**
   * Labels GUARD_COMBINE tree node
   * @param p node to label
   */
  private static void label_GUARD_COMBINE(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: GUARD_COMBINE
    if(BURS.DEBUG) trace(p, 35, 11 + 0, p.getCost(2) /* r */);
    if (11 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(11));
      p.writePacked(0, 0xFFFF00FF, 0x600); // p.r = 6
      closure_r(p, 11);
    }
  }

  /**
   * Labels INT_ADD tree node
   * @param p node to label
   */
  private static void label_INT_ADD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // address: INT_ADD(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 61, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0x60000); // p.address = 3
    }
    // address: INT_ADD(r,address1scaledreg)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(16 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 62, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0x80000); // p.address = 4
    }
    // address: INT_ADD(address1scaledreg,r)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 63, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0xA0000); // p.address = 5
    }
    if ( // address: INT_ADD(address1scaledreg,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1scaledreg */) + 0;
      if(BURS.DEBUG) trace(p, 229, c + 0, p.getCost(15) /* address */);
      if (c < p.getCost(15) /* address */) {
        p.setCost(15 /* address */, (char)(c));
        p.writePacked(1, 0xFFE1FFFF, 0xC0000); // p.address = 6
      }
    }
    // address: INT_ADD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild).getCost(17 /* address1reg */) + 0;
    if(BURS.DEBUG) trace(p, 64, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0xE0000); // p.address = 7
    }
    // address: INT_ADD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(17 /* address1reg */) + STATE(rchild).getCost(16 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 65, c + 0, p.getCost(15) /* address */);
    if (c < p.getCost(15) /* address */) {
      p.setCost(15 /* address */, (char)(c));
      p.writePacked(1, 0xFFE1FFFF, 0x100000); // p.address = 8
    }
    if ( // address1reg: INT_ADD(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 0;
      if(BURS.DEBUG) trace(p, 230, c + 0, p.getCost(17) /* address1reg */);
      if (c < p.getCost(17) /* address1reg */) {
        p.setCost(17 /* address1reg */, (char)(c));
        p.writePacked(1, 0xF8FFFFFF, 0x1000000); // p.address1reg = 1
        closure_address1reg(p, c);
      }
    }
    if ( // address1reg: INT_ADD(address1reg,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address1reg */) + 0;
      if(BURS.DEBUG) trace(p, 233, c + 0, p.getCost(17) /* address1reg */);
      if (c < p.getCost(17) /* address1reg */) {
        p.setCost(17 /* address1reg */, (char)(c));
        p.writePacked(1, 0xF8FFFFFF, 0x4000000); // p.address1reg = 4
        closure_address1reg(p, c);
      }
    }
    if ( // address1scaledreg: INT_ADD(address1scaledreg,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1scaledreg */) + 0;
      if(BURS.DEBUG) trace(p, 236, c + 0, p.getCost(16) /* address1scaledreg */);
      if (c < p.getCost(16) /* address1scaledreg */) {
        p.setCost(16 /* address1scaledreg */, (char)(c));
        p.writePacked(1, 0xFF1FFFFF, 0x800000); // p.address1scaledreg = 4
        closure_address1scaledreg(p, c);
      }
    }
    // czr: INT_ADD(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 74, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x10000); // p.czr = 1
      closure_czr(p, c);
    }
    // r: INT_ADD(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 75, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4E00); // p.r = 78
      closure_r(p, c);
    }
    // czr: INT_ADD(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 76, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x20000); // p.czr = 2
      closure_czr(p, c);
    }
    // czr: INT_ADD(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 77, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x30000); // p.czr = 3
      closure_czr(p, c);
    }
    // r: INT_ADD(address1scaledreg,r)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild).getCost(2 /* r */) + 11;
    if(BURS.DEBUG) trace(p, 123, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x6F00); // p.r = 111
      closure_r(p, c);
    }
    // r: INT_ADD(r,address1scaledreg)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(16 /* address1scaledreg */) + 11;
    if(BURS.DEBUG) trace(p, 124, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7000); // p.r = 112
      closure_r(p, c);
    }
    // r: INT_ADD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild).getCost(17 /* address1reg */) + 11;
    if(BURS.DEBUG) trace(p, 125, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7100); // p.r = 113
      closure_r(p, c);
    }
    // r: INT_ADD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(17 /* address1reg */) + STATE(rchild).getCost(16 /* address1scaledreg */) + 11;
    if(BURS.DEBUG) trace(p, 126, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7200); // p.r = 114
      closure_r(p, c);
    }
    if ( // r: INT_ADD(address,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address */) + 11;
      if(BURS.DEBUG) trace(p, 297, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x7300); // p.r = 115
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels LONG_ADD tree node
   * @param p node to label
   */
  private static void label_LONG_ADD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_ADD(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 26;
    if(BURS.DEBUG) trace(p, 147, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8300); // p.r = 131
      closure_r(p, c);
    }
    // r: LONG_ADD(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(22 /* load64 */) + 30;
    if(BURS.DEBUG) trace(p, 148, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8400); // p.r = 132
      closure_r(p, c);
    }
    // r: LONG_ADD(load64,rlv)
    c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 30;
    if(BURS.DEBUG) trace(p, 149, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8500); // p.r = 133
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_ADD tree node
   * @param p node to label
   */
  private static void label_FLOAT_ADD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: FLOAT_ADD(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 169, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA200); // p.r = 162
      closure_r(p, c);
    }
    // r: FLOAT_ADD(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(25 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 170, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA300); // p.r = 163
      closure_r(p, c);
    }
    // r: FLOAT_ADD(float_load,r)
    c = STATE(lchild).getCost(25 /* float_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 171, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA400); // p.r = 164
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_ADD tree node
   * @param p node to label
   */
  private static void label_DOUBLE_ADD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_ADD(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 172, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA500); // p.r = 165
      closure_r(p, c);
    }
    // r: DOUBLE_ADD(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 173, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA600); // p.r = 166
      closure_r(p, c);
    }
    // r: DOUBLE_ADD(double_load,r)
    c = STATE(lchild).getCost(26 /* double_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 174, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA700); // p.r = 167
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_SUB tree node
   * @param p node to label
   */
  private static void label_INT_SUB(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // czr: INT_SUB(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 114, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x50000); // p.czr = 5
      closure_czr(p, c);
    }
    // r: INT_SUB(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + (Binary.getResult(P(p)).similar(Binary.getVal2(P(p))) ? 13-2 : INFINITE);
    if(BURS.DEBUG) trace(p, 115, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x6C00); // p.r = 108
      closure_r(p, c);
    }
    // r: INT_SUB(load32,r)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(2 /* r */) + (Binary.getResult(P(p)).similar(Binary.getVal2(P(p))) ? 15-2 : INFINITE);
    if(BURS.DEBUG) trace(p, 116, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x6D00); // p.r = 109
      closure_r(p, c);
    }
    // czr: INT_SUB(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 117, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x60000); // p.czr = 6
      closure_czr(p, c);
    }
    // czr: INT_SUB(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 118, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFF8FFFF, 0x70000); // p.czr = 7
      closure_czr(p, c);
    }
  }

  /**
   * Labels LONG_SUB tree node
   * @param p node to label
   */
  private static void label_LONG_SUB(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_SUB(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 23;
    if(BURS.DEBUG) trace(p, 162, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9A00); // p.r = 154
      closure_r(p, c);
    }
    // r: LONG_SUB(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(22 /* load64 */) + 30;
    if(BURS.DEBUG) trace(p, 163, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9B00); // p.r = 155
      closure_r(p, c);
    }
    // r: LONG_SUB(load64,rlv)
    c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 30;
    if(BURS.DEBUG) trace(p, 164, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9C00); // p.r = 156
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_SUB tree node
   * @param p node to label
   */
  private static void label_FLOAT_SUB(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: FLOAT_SUB(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 175, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA800); // p.r = 168
      closure_r(p, c);
    }
    // r: FLOAT_SUB(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(25 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 176, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA900); // p.r = 169
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_SUB tree node
   * @param p node to label
   */
  private static void label_DOUBLE_SUB(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_SUB(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 177, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xAA00); // p.r = 170
      closure_r(p, c);
    }
    // r: DOUBLE_SUB(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 178, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xAB00); // p.r = 171
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_MUL tree node
   * @param p node to label
   */
  private static void label_INT_MUL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: INT_MUL(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 102, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5B00); // p.r = 91
      closure_r(p, c);
    }
    // r: INT_MUL(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 103, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5C00); // p.r = 92
      closure_r(p, c);
    }
    // r: INT_MUL(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 104, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5D00); // p.r = 93
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_MUL tree node
   * @param p node to label
   */
  private static void label_LONG_MUL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_MUL(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 5*13;
    if(BURS.DEBUG) trace(p, 156, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8D00); // p.r = 141
      closure_r(p, c);
    }
    if ( // r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_AND(rlv,LONG_CONSTANT))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == LONG_AND_opcode && 
      rchild.getChild2().getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + ((Binary.getVal2(PL(p)).asLongConstant().upper32() == 0) && (Binary.getVal2(PL(p)).asLongConstant().lower32() == -1)&& (Binary.getVal2(PR(p)).asLongConstant().upper32() == 0) && (Binary.getVal2(PR(p)).asLongConstant().lower32() == -1) ? (4*11) : INFINITE);
      if(BURS.DEBUG) trace(p, 535, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x8E00); // p.r = 142
        closure_r(p, c);
      }
    }
    if ( // r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_CONSTANT)
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + ((Binary.getVal2(P(p)).asLongConstant().upper32() == 0) ? (4*11) : INFINITE);
      if(BURS.DEBUG) trace(p, 352, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x8F00); // p.r = 143
        closure_r(p, c);
      }
    }
    if ( // r: LONG_MUL(INT_2LONG(riv),INT_2LONG(riv))
      lchild.getOpcode() == INT_2LONG_opcode && 
      rchild.getOpcode() == INT_2LONG_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + 4*11;
      if(BURS.DEBUG) trace(p, 536, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x9000); // p.r = 144
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels FLOAT_MUL tree node
   * @param p node to label
   */
  private static void label_FLOAT_MUL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: FLOAT_MUL(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 179, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xAC00); // p.r = 172
      closure_r(p, c);
    }
    // r: FLOAT_MUL(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(25 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 180, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xAD00); // p.r = 173
      closure_r(p, c);
    }
    // r: FLOAT_MUL(float_load,r)
    c = STATE(lchild).getCost(25 /* float_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 181, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xAE00); // p.r = 174
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_MUL tree node
   * @param p node to label
   */
  private static void label_DOUBLE_MUL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_MUL(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 182, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xAF00); // p.r = 175
      closure_r(p, c);
    }
    // r: DOUBLE_MUL(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 183, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB000); // p.r = 176
      closure_r(p, c);
    }
    // r: DOUBLE_MUL(double_load,r)
    c = STATE(lchild).getCost(26 /* double_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 184, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB100); // p.r = 177
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_DIV tree node
   * @param p node to label
   */
  private static void label_INT_DIV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: INT_DIV(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 52;
    if(BURS.DEBUG) trace(p, 84, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4F00); // p.r = 79
      closure_r(p, c);
    }
    // r: INT_DIV(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 85, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5000); // p.r = 80
      closure_r(p, c);
    }
  }

  /**
   * Labels UNSIGNED_DIV_64_32 tree node
   * @param p node to label
   */
  private static void label_UNSIGNED_DIV_64_32(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: UNSIGNED_DIV_64_32(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 52;
    if(BURS.DEBUG) trace(p, 86, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5100); // p.r = 81
      closure_r(p, c);
    }
    // r: UNSIGNED_DIV_64_32(rlv,load32)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 87, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5200); // p.r = 82
      closure_r(p, c);
    }
  }

  /**
   * Labels UNSIGNED_REM_64_32 tree node
   * @param p node to label
   */
  private static void label_UNSIGNED_REM_64_32(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: UNSIGNED_REM_64_32(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 52;
    if(BURS.DEBUG) trace(p, 110, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x6100); // p.r = 97
      closure_r(p, c);
    }
    // r: UNSIGNED_REM_64_32(rlv,load32)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 111, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x6200); // p.r = 98
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_DIV tree node
   * @param p node to label
   */
  private static void label_FLOAT_DIV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: FLOAT_DIV(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 185, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB200); // p.r = 178
      closure_r(p, c);
    }
    // r: FLOAT_DIV(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(25 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 186, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB300); // p.r = 179
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_DIV tree node
   * @param p node to label
   */
  private static void label_DOUBLE_DIV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_DIV(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 187, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB400); // p.r = 180
      closure_r(p, c);
    }
    // r: DOUBLE_DIV(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 188, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB500); // p.r = 181
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_REM tree node
   * @param p node to label
   */
  private static void label_INT_REM(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: INT_REM(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 52;
    if(BURS.DEBUG) trace(p, 108, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5F00); // p.r = 95
      closure_r(p, c);
    }
    // r: INT_REM(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 109, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x6000); // p.r = 96
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_REM tree node
   * @param p node to label
   */
  private static void label_FLOAT_REM(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: FLOAT_REM(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 189, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xBA00); // p.r = 186
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_REM tree node
   * @param p node to label
   */
  private static void label_DOUBLE_REM(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_REM(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 190, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xBB00); // p.r = 187
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_NEG tree node
   * @param p node to label
   */
  private static void label_INT_NEG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // szpr: INT_NEG(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 291, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0xC00000); // p.szpr = 6
      closure_szpr(p, c);
    }
  }

  /**
   * Labels LONG_NEG tree node
   * @param p node to label
   */
  private static void label_LONG_NEG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_NEG(r)
    c = STATE(lchild).getCost(2 /* r */) + 26;
    if(BURS.DEBUG) trace(p, 304, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9100); // p.r = 145
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_NEG tree node
   * @param p node to label
   */
  private static void label_FLOAT_NEG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_NEG(r)
    c = STATE(lchild).getCost(2 /* r */) + 26;
    if(BURS.DEBUG) trace(p, 306, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB600); // p.r = 182
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_NEG tree node
   * @param p node to label
   */
  private static void label_DOUBLE_NEG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_NEG(r)
    c = STATE(lchild).getCost(2 /* r */) + 26;
    if(BURS.DEBUG) trace(p, 307, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB700); // p.r = 183
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_SQRT tree node
   * @param p node to label
   */
  private static void label_FLOAT_SQRT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_SQRT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 308, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB800); // p.r = 184
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_SQRT tree node
   * @param p node to label
   */
  private static void label_DOUBLE_SQRT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_SQRT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 309, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xB900); // p.r = 185
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_SHL tree node
   * @param p node to label
   */
  private static void label_INT_SHL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // address1scaledreg: INT_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + LEA_SHIFT(Binary.getVal2(P(p)), 0);
      if(BURS.DEBUG) trace(p, 235, c + 0, p.getCost(16) /* address1scaledreg */);
      if (c < p.getCost(16) /* address1scaledreg */) {
        p.setCost(16 /* address1scaledreg */, (char)(c));
        p.writePacked(1, 0xFF1FFFFF, 0x600000); // p.address1scaledreg = 3
        closure_address1scaledreg(p, c);
      }
    }
    if ( // szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 31 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 541, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x1400000); // p.szpr = 10
        closure_szpr(p, c);
      }
    }
    // szpr: INT_SHL(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 112, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x1600000); // p.szpr = 11
      closure_szpr(p, c);
    }
    if ( // szpr: INT_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 13;
      if(BURS.DEBUG) trace(p, 293, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x1800000); // p.szpr = 12
        closure_szpr(p, c);
      }
    }
    if ( // r: INT_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (!Binary.getResult(P(p)).similar(Binary.getVal1(P(p))) && (Binary.getVal2(P(p)).asIntConstant().value & 0x1f) <= 3 ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 294, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6B00); // p.r = 107
        closure_r(p, c);
      }
    }
    if ( // szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((VR(p) == VLR(p)) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 345, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x1A00000); // p.szpr = 13
        closure_szpr(p, c);
      }
    }
  }

  /**
   * Labels LONG_SHL tree node
   * @param p node to label
   */
  private static void label_LONG_SHL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: LONG_SHL(INT_2LONG(r),INT_CONSTANT)
      lchild.getOpcode() == INT_2LONG_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + (VR(p) == 32 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 343, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4900); // p.r = 73
        closure_r(p, c);
      }
    }
    if ( // r: LONG_SHL(INT_2LONG(load64),INT_CONSTANT)
      lchild.getOpcode() == INT_2LONG_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(22 /* load64 */) + (VR(p) == 32 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 344, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4A00); // p.r = 74
        closure_r(p, c);
      }
    }
    // r: LONG_SHL(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 160, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9600); // p.r = 150
      closure_r(p, c);
    }
    if ( // r: LONG_SHL(rlv,INT_AND(riv,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + 20;
      if(BURS.DEBUG) trace(p, 545, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x9700); // p.r = 151
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels INT_SHR tree node
   * @param p node to label
   */
  private static void label_INT_SHR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 31 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 542, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x1C00000); // p.szpr = 14
        closure_szpr(p, c);
      }
    }
    // szpr: INT_SHR(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 113, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x1E00000); // p.szpr = 15
      closure_szpr(p, c);
    }
    if ( // szpr: INT_SHR(riv,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + 13;
      if(BURS.DEBUG) trace(p, 295, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x2000000); // p.szpr = 16
        closure_szpr(p, c);
      }
    }
  }

  /**
   * Labels LONG_SHR tree node
   * @param p node to label
   */
  private static void label_LONG_SHR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_SHR(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 161, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9800); // p.r = 152
      closure_r(p, c);
    }
    if ( // r: LONG_SHR(rlv,INT_AND(riv,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + 20;
      if(BURS.DEBUG) trace(p, 546, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x9900); // p.r = 153
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels INT_USHR tree node
   * @param p node to label
   */
  private static void label_INT_USHR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(12 /* load8_16_32 */) + (VR(p) == 24 && VLLR(p) == 24 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 337, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xA00); // p.r = 10
        closure_r(p, c);
      }
    }
    if ( // r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(13 /* load16_32 */) + (VR(p) == 16 && VLR(p) == 16 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 338, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xC00); // p.r = 12
        closure_r(p, c);
      }
    }
    if ( // szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 31 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 544, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x2200000); // p.szpr = 17
        closure_szpr(p, c);
      }
    }
    // szpr: INT_USHR(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 119, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x2400000); // p.szpr = 18
      closure_szpr(p, c);
    }
    if ( // szpr: INT_USHR(riv,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + 13;
      if(BURS.DEBUG) trace(p, 296, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xFC1FFFFF, 0x2600000); // p.szpr = 19
        closure_szpr(p, c);
      }
    }
  }

  /**
   * Labels LONG_USHR tree node
   * @param p node to label
   */
  private static void label_LONG_USHR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_USHR(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 165, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9D00); // p.r = 157
      closure_r(p, c);
    }
    if ( // r: LONG_USHR(rlv,INT_AND(riv,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + 20;
      if(BURS.DEBUG) trace(p, 547, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x9E00); // p.r = 158
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels INT_AND tree node
   * @param p node to label
   */
  private static void label_INT_AND(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // uload8: INT_AND(load8_16_32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(12 /* load8_16_32 */) + (VR(p) == 0xff ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 222, c + 0, p.getCost(11) /* uload8 */);
      if (c < p.getCost(11) /* uload8 */) {
        p.setCost(11 /* uload8 */, (char)(c));
        p.writePacked(1, 0xFFFFF8FF, 0x100); // p.uload8 = 1
        closure_uload8(p, c);
      }
    }
    if ( // r: INT_AND(load8_16_32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(12 /* load8_16_32 */) + (VR(p) == 0xff ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 223, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x800); // p.r = 8
        closure_r(p, c);
      }
    }
    if ( // r: INT_AND(load16_32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(13 /* load16_32 */) + (VR(p) == 0xffff ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 225, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xB00); // p.r = 11
        closure_r(p, c);
      }
    }
    if ( // bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLRR(p) == 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 453, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x8000000); // p.bittest = 1
      }
    }
    if ( // bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(10 /* load32 */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + (VR(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 454, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x10000000); // p.bittest = 2
      }
    }
    if ( // bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLR(p) <= 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 339, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x18000000); // p.bittest = 3
      }
    }
    if ( // bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLRR(p) == 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 455, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x20000000); // p.bittest = 4
      }
    }
    if ( // bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(10 /* load32 */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + (VR(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 456, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x28000000); // p.bittest = 5
      }
    }
    if ( // bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLR(p) <= 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 340, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x30000000); // p.bittest = 6
      }
    }
    if ( // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + ((VLL(p) == 1) && (VLRR(p) == 31)? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 457, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x38000000); // p.bittest = 7
      }
    }
    if ( // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + (VLL(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 458, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x40000000); // p.bittest = 8
      }
    }
    if ( // bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + ((VRL(p) == 1) && (VRRR(p) == 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 459, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x48000000); // p.bittest = 9
      }
    }
    if ( // bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + (VRL(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 460, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(1, 0x87FFFFFF, 0x50000000); // p.bittest = 10
      }
    }
    // szpr: INT_AND(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 78, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x400000); // p.szpr = 2
      closure_szpr(p, c);
    }
    // szp: INT_AND(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 79, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(0, 0xE3FFFFFF, 0x8000000); // p.szp = 2
    }
    // szpr: INT_AND(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 80, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x600000); // p.szpr = 3
      closure_szpr(p, c);
    }
    // szpr: INT_AND(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 81, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x800000); // p.szpr = 4
      closure_szpr(p, c);
    }
    // szp: INT_AND(load8_16_32,riv)
    c = STATE(lchild).getCost(12 /* load8_16_32 */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 82, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(0, 0xE3FFFFFF, 0xC000000); // p.szp = 3
    }
    // szp: INT_AND(r,load8_16_32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(12 /* load8_16_32 */) + 11;
    if(BURS.DEBUG) trace(p, 83, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(0, 0xE3FFFFFF, 0x10000000); // p.szp = 4
    }
  }

  /**
   * Labels LONG_AND tree node
   * @param p node to label
   */
  private static void label_LONG_AND(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
      lchild.getOpcode() == INT_2LONG_opcode && 
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((Binary.getVal2(P(p)).asLongConstant().upper32() == 0) && (Binary.getVal2(P(p)).asLongConstant().lower32() == -1)? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 341, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4700); // p.r = 71
        closure_r(p, c);
      }
    }
    if ( // r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
      lchild.getOpcode() == INT_2LONG_opcode && 
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(10 /* load32 */) + ((Binary.getVal2(P(p)).asLongConstant().upper32() == 0) && (Binary.getVal2(P(p)).asLongConstant().lower32() == -1)? 28 : INFINITE);
      if(BURS.DEBUG) trace(p, 342, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4800); // p.r = 72
        closure_r(p, c);
      }
    }
    // r: LONG_AND(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 26;
    if(BURS.DEBUG) trace(p, 150, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8600); // p.r = 134
      closure_r(p, c);
    }
    // r: LONG_AND(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(22 /* load64 */) + 30;
    if(BURS.DEBUG) trace(p, 151, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8700); // p.r = 135
      closure_r(p, c);
    }
    // r: LONG_AND(load64,rlv)
    c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 30;
    if(BURS.DEBUG) trace(p, 152, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8800); // p.r = 136
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_OR tree node
   * @param p node to label
   */
  private static void label_INT_OR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // szpr: INT_OR(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 105, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0xE00000); // p.szpr = 7
      closure_szpr(p, c);
    }
    // szpr: INT_OR(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 106, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x1000000); // p.szpr = 8
      closure_szpr(p, c);
    }
    // szpr: INT_OR(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 107, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x1200000); // p.szpr = 9
      closure_szpr(p, c);
    }
    if ( // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_USHR_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && ((-VLR(p)) & 0x1f) == (VRR(p)&0x1f) ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 531, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6300); // p.r = 99
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && ((-VRR(p)) & 0x1f) == (VLR(p)&0x1f) ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 532, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6400); // p.r = 100
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_USHR_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && ((-VLR(p)) & 0x1f) == (VRR(p)&0x1f) && ((VLR(p)&0x1f) == 31) ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 533, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6500); // p.r = 101
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && ((-VRR(p)) & 0x1f) == (VLR(p)&0x1f) && ((VRR(p)&0x1f) == 31) ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 534, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6600); // p.r = 102
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_USHR_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == INT_NEG_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && (VLRR(p) == 31) && (VRRR(p) == 31) && Binary.getVal1(PLR(p)).similar(Unary.getVal(PRRL(p))) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 537, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6700); // p.r = 103
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild1().getOpcode() == INT_NEG_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && (VLRR(p) == 31) && (VRRR(p) == 31) && Binary.getVal1(PRR(p)).similar(Unary.getVal(PLRL(p))) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 539, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6800); // p.r = 104
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild1().getOpcode() == INT_NEG_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_USHR_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && (VLRR(p) == 31) && (VRRR(p) == 31) && Binary.getVal1(PRR(p)).similar(Unary.getVal(PLRL(p))) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 540, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6900); // p.r = 105
        closure_r(p, c);
      }
    }
    if ( // r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == INT_NEG_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && (VLRR(p) == 31) && (VRRR(p) == 31) && Binary.getVal1(PLR(p)).similar(Unary.getVal(PRRL(p))) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 538, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6A00); // p.r = 106
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels LONG_OR tree node
   * @param p node to label
   */
  private static void label_LONG_OR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_OR(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 26;
    if(BURS.DEBUG) trace(p, 157, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9300); // p.r = 147
      closure_r(p, c);
    }
    // r: LONG_OR(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(22 /* load64 */) + 30;
    if(BURS.DEBUG) trace(p, 158, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9400); // p.r = 148
      closure_r(p, c);
    }
    // r: LONG_OR(load64,rlv)
    c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 30;
    if(BURS.DEBUG) trace(p, 159, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9500); // p.r = 149
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_XOR tree node
   * @param p node to label
   */
  private static void label_INT_XOR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // szpr: INT_XOR(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 120, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x2800000); // p.szpr = 20
      closure_szpr(p, c);
    }
    // szpr: INT_XOR(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 121, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x2A00000); // p.szpr = 21
      closure_szpr(p, c);
    }
    // szpr: INT_XOR(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 122, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x2C00000); // p.szpr = 22
      closure_szpr(p, c);
    }
  }

  /**
   * Labels INT_NOT tree node
   * @param p node to label
   */
  private static void label_INT_NOT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_NOT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 292, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5E00); // p.r = 94
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_NOT tree node
   * @param p node to label
   */
  private static void label_LONG_NOT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_NOT(r)
    c = STATE(lchild).getCost(2 /* r */) + 26;
    if(BURS.DEBUG) trace(p, 305, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9200); // p.r = 146
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_XOR tree node
   * @param p node to label
   */
  private static void label_LONG_XOR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_XOR(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 26;
    if(BURS.DEBUG) trace(p, 166, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x9F00); // p.r = 159
      closure_r(p, c);
    }
    // r: LONG_XOR(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(22 /* load64 */) + 30;
    if(BURS.DEBUG) trace(p, 167, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA000); // p.r = 160
      closure_r(p, c);
    }
    // r: LONG_XOR(load64,rlv)
    c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 30;
    if(BURS.DEBUG) trace(p, 168, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xA100); // p.r = 161
      closure_r(p, c);
    }
  }

  /**
   * Labels ADDR_2LONG tree node
   * @param p node to label
   */
  private static void label_ADDR_2LONG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: ADDR_2LONG(r)
    c = STATE(lchild).getCost(2 /* r */) + 33;
    if(BURS.DEBUG) trace(p, 237, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x1700); // p.r = 23
      closure_r(p, c);
    }
    // r: ADDR_2LONG(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 38;
    if(BURS.DEBUG) trace(p, 238, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x1800); // p.r = 24
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_2LONG tree node
   * @param p node to label
   */
  private static void label_INT_2LONG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_2LONG(r)
    c = STATE(lchild).getCost(2 /* r */) + 33;
    if(BURS.DEBUG) trace(p, 262, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4500); // p.r = 69
      closure_r(p, c);
    }
    // r: INT_2LONG(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 38;
    if(BURS.DEBUG) trace(p, 263, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4600); // p.r = 70
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_2FLOAT tree node
   * @param p node to label
   */
  private static void label_INT_2FLOAT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_2FLOAT(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 314, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xCD00); // p.r = 205
      closure_r(p, c);
    }
    // r: INT_2FLOAT(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 315, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xCE00); // p.r = 206
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_2DOUBLE tree node
   * @param p node to label
   */
  private static void label_INT_2DOUBLE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_2DOUBLE(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 316, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xCF00); // p.r = 207
      closure_r(p, c);
    }
    // r: INT_2DOUBLE(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 317, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD000); // p.r = 208
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_2INT tree node
   * @param p node to label
   */
  private static void label_LONG_2INT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_2INT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 299, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7D00); // p.r = 125
      closure_r(p, c);
    }
    // r: LONG_2INT(load64)
    c = STATE(lchild).getCost(22 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 300, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7E00); // p.r = 126
      closure_r(p, c);
    }
    // load32: LONG_2INT(load64)
    c = STATE(lchild).getCost(22 /* load64 */) + 0;
    if(BURS.DEBUG) trace(p, 301, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFFF1F, 0x80); // p.load32 = 4
      closure_load32(p, c);
    }
    if ( // r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + (VLR(p) == 32 ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 346, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x7F00); // p.r = 127
        closure_r(p, c);
      }
    }
    if ( // r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + (VLR(p) == 32 ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 347, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x8000); // p.r = 128
        closure_r(p, c);
      }
    }
    if ( // r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(22 /* load64 */) + (VLR(p) == 32 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 348, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x8100); // p.r = 129
        closure_r(p, c);
      }
    }
    if ( // r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(22 /* load64 */) + (VLR(p) == 32 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 349, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x8200); // p.r = 130
        closure_r(p, c);
      }
    }
    if ( // load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(22 /* load64 */) + (VLR(p) == 32 ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 350, c + 0, p.getCost(10) /* load32 */);
      if (c < p.getCost(10) /* load32 */) {
        p.setCost(10 /* load32 */, (char)(c));
        p.writePacked(1, 0xFFFFFF1F, 0xA0); // p.load32 = 5
        closure_load32(p, c);
      }
    }
    if ( // load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(22 /* load64 */) + (VLR(p) == 32 ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 351, c + 0, p.getCost(10) /* load32 */);
      if (c < p.getCost(10) /* load32 */) {
        p.setCost(10 /* load32 */, (char)(c));
        p.writePacked(1, 0xFFFFFF1F, 0xC0); // p.load32 = 6
        closure_load32(p, c);
      }
    }
  }

  /**
   * Labels LONG_2FLOAT tree node
   * @param p node to label
   */
  private static void label_LONG_2FLOAT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_2FLOAT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 310, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xBC00); // p.r = 188
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_2DOUBLE tree node
   * @param p node to label
   */
  private static void label_LONG_2DOUBLE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_2DOUBLE(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 311, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xBD00); // p.r = 189
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_2INT tree node
   * @param p node to label
   */
  private static void label_FLOAT_2INT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_2INT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 322, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD500); // p.r = 213
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_2LONG tree node
   * @param p node to label
   */
  private static void label_FLOAT_2LONG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_2LONG(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 323, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD600); // p.r = 214
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_2DOUBLE tree node
   * @param p node to label
   */
  private static void label_FLOAT_2DOUBLE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_2DOUBLE(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 318, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD100); // p.r = 209
      closure_r(p, c);
    }
    // r: FLOAT_2DOUBLE(float_load)
    c = STATE(lchild).getCost(25 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 319, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD200); // p.r = 210
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_2INT tree node
   * @param p node to label
   */
  private static void label_DOUBLE_2INT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_2INT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 324, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD700); // p.r = 215
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_2LONG tree node
   * @param p node to label
   */
  private static void label_DOUBLE_2LONG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_2LONG(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 325, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD800); // p.r = 216
      closure_r(p, c);
    }
  }

  /**
   * Labels DOUBLE_2FLOAT tree node
   * @param p node to label
   */
  private static void label_DOUBLE_2FLOAT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_2FLOAT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 320, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD300); // p.r = 211
      closure_r(p, c);
    }
    // r: DOUBLE_2FLOAT(double_load)
    c = STATE(lchild).getCost(26 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 321, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD400); // p.r = 212
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_2BYTE tree node
   * @param p node to label
   */
  private static void label_INT_2BYTE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_2BYTE(load8_16_32)
    c = STATE(lchild).getCost(12 /* load8_16_32 */) + 20;
    if(BURS.DEBUG) trace(p, 224, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x900); // p.r = 9
      closure_r(p, c);
    }
    // r: INT_2BYTE(r)
    c = STATE(lchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 260, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4300); // p.r = 67
      closure_r(p, c);
    }
    // r: INT_2BYTE(load8_16_32)
    c = STATE(lchild).getCost(12 /* load8_16_32 */) + 17;
    if(BURS.DEBUG) trace(p, 261, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4400); // p.r = 68
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_2USHORT tree node
   * @param p node to label
   */
  private static void label_INT_2USHORT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // szpr: INT_2USHORT(r)
    c = STATE(lchild).getCost(2 /* r */) + 23;
    if(BURS.DEBUG) trace(p, 267, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xFC1FFFFF, 0x200000); // p.szpr = 1
      closure_szpr(p, c);
    }
    // uload16: INT_2USHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 0;
    if(BURS.DEBUG) trace(p, 268, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x1000); // p.uload16 = 1
      closure_uload16(p, c);
    }
    // r: INT_2USHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 15;
    if(BURS.DEBUG) trace(p, 269, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4D00); // p.r = 77
      closure_r(p, c);
    }
  }

  /**
   * Labels INT_2SHORT tree node
   * @param p node to label
   */
  private static void label_INT_2SHORT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_2SHORT(r)
    c = STATE(lchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 264, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4B00); // p.r = 75
      closure_r(p, c);
    }
    // r: INT_2SHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 17;
    if(BURS.DEBUG) trace(p, 265, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x4C00); // p.r = 76
      closure_r(p, c);
    }
    // sload16: INT_2SHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 0;
    if(BURS.DEBUG) trace(p, 266, c + 0, p.getCost(21) /* sload16 */);
    if (c < p.getCost(21) /* sload16 */) {
      p.setCost(21 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFFFFE3F, 0x40); // p.sload16 = 1
      closure_sload16(p, c);
    }
  }

  /**
   * Labels LONG_CMP tree node
   * @param p node to label
   */
  private static void label_LONG_CMP(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_CMP(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 10*13;
    if(BURS.DEBUG) trace(p, 57, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD00); // p.r = 13
      closure_r(p, c);
    }
  }

  /**
   * Labels RETURN tree node
   * @param p node to label
   */
  private static void label_RETURN(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    if ( // stm: RETURN(NULL)
      lchild.getOpcode() == NULL_opcode  
    ) {
      c = 13;
      if(BURS.DEBUG) trace(p, 47, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x2E); // p.stm = 46
      }
    }
    if ( // stm: RETURN(INT_CONSTANT)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = 11;
      if(BURS.DEBUG) trace(p, 48, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x2F); // p.stm = 47
      }
    }
    // stm: RETURN(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 227, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x30); // p.stm = 48
    }
    if ( // stm: RETURN(LONG_CONSTANT)
      lchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = 11;
      if(BURS.DEBUG) trace(p, 49, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x31); // p.stm = 49
      }
    }
  }

  /**
   * Labels NULL_CHECK tree node
   * @param p node to label
   */
  private static void label_NULL_CHECK(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // stm: NULL_CHECK(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 218, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xB); // p.stm = 11
    }
  }

  /**
   * Labels GOTO tree node
   * @param p node to label
   */
  private static void label_GOTO(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: GOTO
    if(BURS.DEBUG) trace(p, 41, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0x27); // p.stm = 39
    }
  }

  /**
   * Labels BOOLEAN_NOT tree node
   * @param p node to label
   */
  private static void label_BOOLEAN_NOT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: BOOLEAN_NOT(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 255, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x3100); // p.r = 49
      closure_r(p, c);
    }
  }

  /**
   * Labels BOOLEAN_CMP_INT tree node
   * @param p node to label
   */
  private static void label_BOOLEAN_CMP_INT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: BOOLEAN_CMP_INT(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 39;
    if(BURS.DEBUG) trace(p, 66, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x2300); // p.r = 35
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_INT(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 67, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x1); // p.boolcmp = 1
    }
    if ( // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && CMP_TO_TEST(BooleanCmp.getCond(P(p))) ? 37:INFINITE);
      if(BURS.DEBUG) trace(p, 239, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2400); // p.r = 36
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && CMP_TO_TEST(BooleanCmp.getCond(P(p))) ? 11:INFINITE);
      if(BURS.DEBUG) trace(p, 240, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x2); // p.boolcmp = 2
      }
    }
    if ( // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isLESS() ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 241, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2500); // p.r = 37
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isLESS() ? 16 : INFINITE);
      if(BURS.DEBUG) trace(p, 242, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2600); // p.r = 38
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isGREATER_EQUAL() ? 22 : INFINITE);
      if(BURS.DEBUG) trace(p, 243, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2700); // p.r = 39
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isGREATER_EQUAL() ? 27 : INFINITE);
      if(BURS.DEBUG) trace(p, 244, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2800); // p.r = 40
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + isZERO(VR(p), 26);
      if(BURS.DEBUG) trace(p, 245, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2900); // p.r = 41
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + isZERO(VR(p), 0);
      if(BURS.DEBUG) trace(p, 246, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x3); // p.boolcmp = 3
      }
    }
    if ( // r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + (VR(p) == 0 && EQ_NE(BooleanCmp.getCond(P(p)))?26:INFINITE);
      if(BURS.DEBUG) trace(p, 247, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2A00); // p.r = 42
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + (VR(p) == 0 && EQ_NE(BooleanCmp.getCond(P(p)))?0:INFINITE);
      if(BURS.DEBUG) trace(p, 248, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x4); // p.boolcmp = 4
      }
    }
    if ( // r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + ((VR(p) == 0 || VR(p) == 1) && EQ_NE(BooleanCmp.getCond(P(p))) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 249, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2B00); // p.r = 43
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + ((VR(p) == 0 || VR(p) == 1) && EQ_NE(BooleanCmp.getCond(P(p))) ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 250, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x5); // p.boolcmp = 5
      }
    }
    if ( // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 1 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 251, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2C00); // p.r = 44
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 1 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 252, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x6); // p.boolcmp = 6
      }
    }
    if ( // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 1 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 0 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 253, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2D00); // p.r = 45
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 1 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 0 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 254, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x7); // p.boolcmp = 7
      }
    }
    // r: BOOLEAN_CMP_INT(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 41;
    if(BURS.DEBUG) trace(p, 68, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x2E00); // p.r = 46
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_INT(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 69, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x8); // p.boolcmp = 8
    }
    // r: BOOLEAN_CMP_INT(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 41;
    if(BURS.DEBUG) trace(p, 70, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x2F00); // p.r = 47
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_INT(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 71, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x9); // p.boolcmp = 9
    }
  }

  /**
   * Labels BOOLEAN_CMP_LONG tree node
   * @param p node to label
   */
  private static void label_BOOLEAN_CMP_LONG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: BOOLEAN_CMP_LONG(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 8*13;
    if(BURS.DEBUG) trace(p, 72, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x3000); // p.r = 48
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_LONG(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 11*13;
    if(BURS.DEBUG) trace(p, 73, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0xA); // p.boolcmp = 10
    }
  }

  /**
   * Labels BYTE_LOAD tree node
   * @param p node to label
   */
  private static void label_BYTE_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: BYTE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 127, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7500); // p.r = 117
      closure_r(p, c);
    }
    // sload8: BYTE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 128, c + 0, p.getCost(24) /* sload8 */);
    if (c < p.getCost(24) /* sload8 */) {
      p.setCost(24 /* sload8 */, (char)(c));
      p.writePacked(2, 0xFFFE7FFF, 0x10000); // p.sload8 = 2
      closure_sload8(p, c);
    }
  }

  /**
   * Labels UBYTE_LOAD tree node
   * @param p node to label
   */
  private static void label_UBYTE_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: UBYTE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 131, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7700); // p.r = 119
      closure_r(p, c);
    }
    // uload8: UBYTE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 132, c + 0, p.getCost(11) /* uload8 */);
    if (c < p.getCost(11) /* uload8 */) {
      p.setCost(11 /* uload8 */, (char)(c));
      p.writePacked(1, 0xFFFFF8FF, 0x300); // p.uload8 = 3
      closure_uload8(p, c);
    }
  }

  /**
   * Labels SHORT_LOAD tree node
   * @param p node to label
   */
  private static void label_SHORT_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: SHORT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 135, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7900); // p.r = 121
      closure_r(p, c);
    }
    // sload16: SHORT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 136, c + 0, p.getCost(21) /* sload16 */);
    if (c < p.getCost(21) /* sload16 */) {
      p.setCost(21 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFFFFE3F, 0xC0); // p.sload16 = 3
      closure_sload16(p, c);
    }
  }

  /**
   * Labels USHORT_LOAD tree node
   * @param p node to label
   */
  private static void label_USHORT_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: USHORT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 139, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x7B00); // p.r = 123
      closure_r(p, c);
    }
    // uload16: USHORT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 140, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x3000); // p.uload16 = 3
      closure_uload16(p, c);
    }
  }

  /**
   * Labels INT_LOAD tree node
   * @param p node to label
   */
  private static void label_INT_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: INT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 96, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5300); // p.r = 83
      closure_r(p, c);
    }
    // r: INT_LOAD(riv,address1scaledreg)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(16 /* address1scaledreg */) + 15;
    if(BURS.DEBUG) trace(p, 97, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5400); // p.r = 84
      closure_r(p, c);
    }
    // r: INT_LOAD(address1scaledreg,riv)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 98, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5500); // p.r = 85
      closure_r(p, c);
    }
    // r: INT_LOAD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild).getCost(17 /* address1reg */) + 15;
    if(BURS.DEBUG) trace(p, 99, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5600); // p.r = 86
      closure_r(p, c);
    }
    // r: INT_LOAD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(17 /* address1reg */) + STATE(rchild).getCost(16 /* address1scaledreg */) + 15;
    if(BURS.DEBUG) trace(p, 100, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x5700); // p.r = 87
      closure_r(p, c);
    }
    if ( // r: INT_LOAD(address,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address */) + 15;
      if(BURS.DEBUG) trace(p, 278, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x5800); // p.r = 88
        closure_r(p, c);
      }
    }
    // load32: INT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 143, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFFF1F, 0x40); // p.load32 = 2
      closure_load32(p, c);
    }
  }

  /**
   * Labels LONG_LOAD tree node
   * @param p node to label
   */
  private static void label_LONG_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // load64: LONG_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 145, c + 0, p.getCost(22) /* load64 */);
    if (c < p.getCost(22) /* load64 */) {
      p.setCost(22 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFFF1FF, 0x200); // p.load64 = 1
    }
    // r: LONG_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 30;
    if(BURS.DEBUG) trace(p, 154, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x8900); // p.r = 137
      closure_r(p, c);
    }
  }

  /**
   * Labels FLOAT_LOAD tree node
   * @param p node to label
   */
  private static void label_FLOAT_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: FLOAT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 202, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC700); // p.r = 199
      closure_r(p, c);
    }
    // r: FLOAT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 203, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC800); // p.r = 200
      closure_r(p, c);
    }
    // float_load: FLOAT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 204, c + 0, p.getCost(25) /* float_load */);
    if (c < p.getCost(25) /* float_load */) {
      p.setCost(25 /* float_load */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x20000); // p.float_load = 1
    }
  }

  /**
   * Labels DOUBLE_LOAD tree node
   * @param p node to label
   */
  private static void label_DOUBLE_LOAD(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: DOUBLE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 191, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC000); // p.r = 192
      closure_r(p, c);
    }
    // r: DOUBLE_LOAD(riv,rlv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 192, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC100); // p.r = 193
      closure_r(p, c);
    }
    // r: DOUBLE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 193, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xC200); // p.r = 194
      closure_r(p, c);
    }
    // double_load: DOUBLE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 194, c + 0, p.getCost(26) /* double_load */);
    if (c < p.getCost(26) /* double_load */) {
      p.setCost(26 /* double_load */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x100000); // p.double_load = 1
    }
    // double_load: DOUBLE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 197, c + 0, p.getCost(26) /* double_load */);
    if (c < p.getCost(26) /* double_load */) {
      p.setCost(26 /* double_load */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x200000); // p.double_load = 2
    }
  }

  /**
   * Labels BYTE_STORE tree node
   * @param p node to label
   */
  private static void label_BYTE_STORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 368, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x41); // p.stm = 65
      }
    }
    if ( // stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == BOOLEAN_NOT_opcode && 
      lchild.getChild1().getOpcode() == UBYTE_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 461, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x43); // p.stm = 67
      }
    }
    if ( // stm: BYTE_STORE(riv,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 370, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x45); // p.stm = 69
      }
    }
    if ( // stm: BYTE_STORE(load8,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load8 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 371, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x46); // p.stm = 70
      }
    }
    if ( // stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2BYTE_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 485, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x49); // p.stm = 73
      }
    }
  }

  /**
   * Labels SHORT_STORE tree node
   * @param p node to label
   */
  private static void label_SHORT_STORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 353, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x16); // p.stm = 22
      }
    }
    if ( // stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(14 /* load16 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 354, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x17); // p.stm = 23
      }
    }
    if ( // stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 355, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x18); // p.stm = 24
      }
    }
    if ( // stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 356, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x19); // p.stm = 25
      }
    }
    if ( // stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2SHORT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 487, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4B); // p.stm = 75
      }
    }
    if ( // stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2USHORT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 489, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4D); // p.stm = 77
      }
    }
  }

  /**
   * Labels INT_STORE tree node
   * @param p node to label
   */
  private static void label_INT_STORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_ADD_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 493, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4F); // p.stm = 79
      }
    }
    if ( // stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_ADD_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 513, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x50); // p.stm = 80
      }
    }
    if ( // stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 495, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x53); // p.stm = 83
      }
    }
    if ( // stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 515, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x54); // p.stm = 84
      }
    }
    if ( // stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NEG_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 463, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x67); // p.stm = 103
      }
    }
    if ( // stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NOT_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 465, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x69); // p.stm = 105
      }
    }
    if ( // stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 497, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6B); // p.stm = 107
      }
    }
    if ( // stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 517, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6C); // p.stm = 108
      }
    }
    if ( // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 31 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 548, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6F); // p.stm = 111
      }
    }
    if ( // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 467, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x70); // p.stm = 112
      }
    }
    if ( // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 31 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 550, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x73); // p.stm = 115
      }
    }
    if ( // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 469, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x74); // p.stm = 116
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 379, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x77); // p.stm = 119
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(riv,address1scaledreg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(16 /* address1scaledreg */) + 15;
      if(BURS.DEBUG) trace(p, 380, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x78); // p.stm = 120
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 381, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x79); // p.stm = 121
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(rchild.getChild2()).getCost(17 /* address1reg */) + 15;
      if(BURS.DEBUG) trace(p, 382, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7A); // p.stm = 122
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(17 /* address1reg */) + STATE(rchild.getChild2()).getCost(16 /* address1scaledreg */) + 15;
      if(BURS.DEBUG) trace(p, 383, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7B); // p.stm = 123
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address,INT_CONSTANT))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(15 /* address */) + 15;
      if(BURS.DEBUG) trace(p, 543, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7C); // p.stm = 124
      }
    }
    if ( // stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 499, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7D); // p.stm = 125
      }
    }
    if ( // stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 27);
      if(BURS.DEBUG) trace(p, 519, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7E); // p.stm = 126
      }
    }
    if ( // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 31 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 552, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x81); // p.stm = 129
      }
    }
    if ( // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 471, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x82); // p.stm = 130
      }
    }
    if ( // stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 501, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x85); // p.stm = 133
      }
    }
    if ( // stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 521, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x86); // p.stm = 134
      }
    }
    if ( // stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_2INT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 491, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x89); // p.stm = 137
      }
    }
  }

  /**
   * Labels LONG_STORE tree node
   * @param p node to label
   */
  private static void label_LONG_STORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_ADD_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 503, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8B); // p.stm = 139
      }
    }
    if ( // stm: LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_ADD_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 523, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8C); // p.stm = 140
      }
    }
    if ( // stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 505, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8F); // p.stm = 143
      }
    }
    if ( // stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 525, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x90); // p.stm = 144
      }
    }
    if ( // stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NEG_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 473, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x94); // p.stm = 148
      }
    }
    if ( // stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NOT_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 475, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x96); // p.stm = 150
      }
    }
    if ( // stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 507, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x98); // p.stm = 152
      }
    }
    if ( // stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 527, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x99); // p.stm = 153
      }
    }
    if ( // stm: LONG_STORE(r,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 30;
      if(BURS.DEBUG) trace(p, 385, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9C); // p.stm = 156
      }
    }
    if ( // stm: LONG_STORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 26;
      if(BURS.DEBUG) trace(p, 418, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9D); // p.stm = 157
      }
    }
    if ( // stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_SUB_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 509, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9E); // p.stm = 158
      }
    }
    if ( // stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 34);
      if(BURS.DEBUG) trace(p, 511, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA0); // p.stm = 160
      }
    }
    if ( // stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 34);
      if(BURS.DEBUG) trace(p, 529, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA1); // p.stm = 161
      }
    }
    if ( // stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 414, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBF); // p.stm = 191
      }
    }
    if ( // stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(22 /* load64 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 415, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC0); // p.stm = 192
      }
    }
  }

  /**
   * Labels FLOAT_STORE tree node
   * @param p node to label
   */
  private static void label_FLOAT_STORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 395, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAD); // p.stm = 173
      }
    }
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 396, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAE); // p.stm = 174
      }
    }
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 397, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAF); // p.stm = 175
      }
    }
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 398, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB0); // p.stm = 176
      }
    }
  }

  /**
   * Labels DOUBLE_STORE tree node
   * @param p node to label
   */
  private static void label_DOUBLE_STORE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 386, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA4); // p.stm = 164
      }
    }
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 387, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA5); // p.stm = 165
      }
    }
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 388, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA6); // p.stm = 166
      }
    }
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 389, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA7); // p.stm = 167
      }
    }
  }

  /**
   * Labels ATTEMPT_INT tree node
   * @param p node to label
   */
  private static void label_ATTEMPT_INT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 425, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1900); // p.r = 25
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 426, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1A00); // p.r = 26
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 427, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1B00); // p.r = 27
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 428, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1C00); // p.r = 28
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 429, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1D00); // p.r = 29
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1scaledreg */) + STATE(rchild.getChild1()).getCost(17 /* address1reg */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 430, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1E00); // p.r = 30
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address1reg */) + STATE(rchild.getChild1()).getCost(16 /* address1scaledreg */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 431, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1F00); // p.r = 31
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 437, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2000); // p.r = 32
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
      lchild.getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(15 /* address */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 438, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2100); // p.r = 33
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels ATTEMPT_LONG tree node
   * @param p node to label
   */
  private static void label_ATTEMPT_LONG(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: ATTEMPT_LONG(riv,OTHER_OPERAND(riv,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 432, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x2200); // p.r = 34
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels CALL tree node
   * @param p node to label
   */
  private static void label_CALL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: CALL(r,any)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(9 /* any */) + 13;
    if(BURS.DEBUG) trace(p, 58, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xE00); // p.r = 14
      closure_r(p, c);
    }
    if ( // r: CALL(BRANCH_TARGET,any)
      lchild.getOpcode() == BRANCH_TARGET_opcode  
    ) {
      c = STATE(rchild).getCost(9 /* any */) + 13;
      if(BURS.DEBUG) trace(p, 419, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF00); // p.r = 15
        closure_r(p, c);
      }
    }
    if ( // r: CALL(INT_LOAD(riv,riv),any)
      lchild.getOpcode() == INT_LOAD_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild).getCost(9 /* any */) + 11;
      if(BURS.DEBUG) trace(p, 422, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1000); // p.r = 16
        closure_r(p, c);
      }
    }
    if ( // r: CALL(INT_CONSTANT,any)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(rchild).getCost(9 /* any */) + 23;
      if(BURS.DEBUG) trace(p, 420, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1100); // p.r = 17
        closure_r(p, c);
      }
    }
    if ( // r: CALL(LONG_LOAD(rlv,rlv),any)
      lchild.getOpcode() == LONG_LOAD_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild).getCost(9 /* any */) + 11;
      if(BURS.DEBUG) trace(p, 423, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1200); // p.r = 18
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels SYSCALL tree node
   * @param p node to label
   */
  private static void label_SYSCALL(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: SYSCALL(r,any)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(9 /* any */) + 13;
    if(BURS.DEBUG) trace(p, 59, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0x1300); // p.r = 19
      closure_r(p, c);
    }
    if ( // r: SYSCALL(INT_LOAD(riv,riv),any)
      lchild.getOpcode() == INT_LOAD_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild).getCost(9 /* any */) + 11;
      if(BURS.DEBUG) trace(p, 424, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1400); // p.r = 20
        closure_r(p, c);
      }
    }
    if ( // r: SYSCALL(INT_CONSTANT,any)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(rchild).getCost(9 /* any */) + 23;
      if(BURS.DEBUG) trace(p, 421, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x1500); // p.r = 21
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels YIELDPOINT_PROLOGUE tree node
   * @param p node to label
   */
  private static void label_YIELDPOINT_PROLOGUE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: YIELDPOINT_PROLOGUE
    if(BURS.DEBUG) trace(p, 28, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x5); // p.stm = 5
    }
  }

  /**
   * Labels YIELDPOINT_EPILOGUE tree node
   * @param p node to label
   */
  private static void label_YIELDPOINT_EPILOGUE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: YIELDPOINT_EPILOGUE
    if(BURS.DEBUG) trace(p, 29, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x6); // p.stm = 6
    }
  }

  /**
   * Labels YIELDPOINT_BACKEDGE tree node
   * @param p node to label
   */
  private static void label_YIELDPOINT_BACKEDGE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: YIELDPOINT_BACKEDGE
    if(BURS.DEBUG) trace(p, 30, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x7); // p.stm = 7
    }
  }

  /**
   * Labels YIELDPOINT_OSR tree node
   * @param p node to label
   */
  private static void label_YIELDPOINT_OSR(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // stm: YIELDPOINT_OSR(any,any)
    c = STATE(lchild).getCost(9 /* any */) + STATE(rchild).getCost(9 /* any */) + 10;
    if(BURS.DEBUG) trace(p, 60, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x32); // p.stm = 50
    }
  }

  /**
   * Labels IR_PROLOGUE tree node
   * @param p node to label
   */
  private static void label_IR_PROLOGUE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: IR_PROLOGUE
    if(BURS.DEBUG) trace(p, 36, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0xC); // p.stm = 12
    }
  }

  /**
   * Labels RESOLVE tree node
   * @param p node to label
   */
  private static void label_RESOLVE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: RESOLVE
    if(BURS.DEBUG) trace(p, 32, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x9); // p.stm = 9
    }
  }

  /**
   * Labels GET_TIME_BASE tree node
   * @param p node to label
   */
  private static void label_GET_TIME_BASE(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: GET_TIME_BASE
    if(BURS.DEBUG) trace(p, 50, 15 + 0, p.getCost(2) /* r */);
    if (15 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(15));
      p.writePacked(0, 0xFFFF00FF, 0x1600); // p.r = 22
      closure_r(p, 15);
    }
  }

  /**
   * Labels TRAP_IF tree node
   * @param p node to label
   */
  private static void label_TRAP_IF(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // stm: TRAP_IF(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 220, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x11); // p.stm = 17
      }
    }
    if ( // stm: TRAP_IF(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 221, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x12); // p.stm = 18
      }
    }
    // stm: TRAP_IF(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 54, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x13); // p.stm = 19
    }
    // stm: TRAP_IF(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 55, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x14); // p.stm = 20
    }
    // stm: TRAP_IF(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 56, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x15); // p.stm = 21
    }
  }

  /**
   * Labels TRAP tree node
   * @param p node to label
   */
  private static void label_TRAP(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: TRAP
    if(BURS.DEBUG) trace(p, 40, 10 + 0, p.getCost(1) /* stm */);
    if (10 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(10));
      p.writePacked(0, 0xFFFFFF00, 0x10); // p.stm = 16
    }
  }

  /**
   * Labels ILLEGAL_INSTRUCTION tree node
   * @param p node to label
   */
  private static void label_ILLEGAL_INSTRUCTION(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: ILLEGAL_INSTRUCTION
    if(BURS.DEBUG) trace(p, 46, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0x2D); // p.stm = 45
    }
  }

  /**
   * Labels FLOAT_AS_INT_BITS tree node
   * @param p node to label
   */
  private static void label_FLOAT_AS_INT_BITS(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: FLOAT_AS_INT_BITS(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 326, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xD900); // p.r = 217
      closure_r(p, c);
    }
    // load32: FLOAT_AS_INT_BITS(float_load)
    c = STATE(lchild).getCost(25 /* float_load */) + 0;
    if(BURS.DEBUG) trace(p, 327, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFFF1F, 0xE0); // p.load32 = 7
      closure_load32(p, c);
    }
  }

  /**
   * Labels INT_BITS_AS_FLOAT tree node
   * @param p node to label
   */
  private static void label_INT_BITS_AS_FLOAT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_BITS_AS_FLOAT(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 330, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xDB00); // p.r = 219
      closure_r(p, c);
    }
    // float_load: INT_BITS_AS_FLOAT(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 0;
    if(BURS.DEBUG) trace(p, 331, c + 0, p.getCost(25) /* float_load */);
    if (c < p.getCost(25) /* float_load */) {
      p.setCost(25 /* float_load */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x80000); // p.float_load = 4
    }
  }

  /**
   * Labels DOUBLE_AS_LONG_BITS tree node
   * @param p node to label
   */
  private static void label_DOUBLE_AS_LONG_BITS(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: DOUBLE_AS_LONG_BITS(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 328, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xDA00); // p.r = 218
      closure_r(p, c);
    }
    // load64: DOUBLE_AS_LONG_BITS(double_load)
    c = STATE(lchild).getCost(26 /* double_load */) + 0;
    if(BURS.DEBUG) trace(p, 329, c + 0, p.getCost(22) /* load64 */);
    if (c < p.getCost(22) /* load64 */) {
      p.setCost(22 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFFF1FF, 0x800); // p.load64 = 4
    }
  }

  /**
   * Labels LONG_BITS_AS_DOUBLE tree node
   * @param p node to label
   */
  private static void label_LONG_BITS_AS_DOUBLE(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: LONG_BITS_AS_DOUBLE(rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 332, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xDC00); // p.r = 220
      closure_r(p, c);
    }
    // double_load: LONG_BITS_AS_DOUBLE(load64)
    c = STATE(lchild).getCost(22 /* load64 */) + 0;
    if(BURS.DEBUG) trace(p, 333, c + 0, p.getCost(26) /* double_load */);
    if (c < p.getCost(26) /* double_load */) {
      p.setCost(26 /* double_load */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x500000); // p.double_load = 5
    }
  }

  /**
   * Labels FRAMESIZE tree node
   * @param p node to label
   */
  private static void label_FRAMESIZE(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: FRAMESIZE
    if(BURS.DEBUG) trace(p, 31, 10 + 0, p.getCost(2) /* r */);
    if (10 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(10));
      p.writePacked(0, 0xFFFF00FF, 0x400); // p.r = 4
      closure_r(p, 10);
    }
  }

  /**
   * Labels LOWTABLESWITCH tree node
   * @param p node to label
   */
  private static void label_LOWTABLESWITCH(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // stm: LOWTABLESWITCH(r)
    c = STATE(lchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 217, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x8); // p.stm = 8
    }
  }

  /**
   * Labels ADDRESS_CONSTANT tree node
   * @param p node to label
   */
  private static void label_ADDRESS_CONSTANT(AbstractBURS_TreeNode p) {
    p.initCost();
    // any: ADDRESS_CONSTANT
    if(BURS.DEBUG) trace(p, 23, 0 + 0, p.getCost(9) /* any */);
    if (0 < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(0));
      p.writePacked(1, 0xFFFFFFE3, 0xC); // p.any = 3
    }
  }

  /**
   * Labels INT_CONSTANT tree node
   * @param p node to label
   */
  private static void label_INT_CONSTANT(AbstractBURS_TreeNode p) {
    p.initCost();
    // riv: INT_CONSTANT
    if(BURS.DEBUG) trace(p, 20, 0 + 0, p.getCost(7) /* riv */);
    if (0 < p.getCost(7) /* riv */) {
      p.setCost(7 /* riv */, (char)(0));
      p.writePacked(0, 0x9FFFFFFF, 0x40000000); // p.riv = 2
      closure_riv(p, 0);
    }
  }

  /**
   * Labels LONG_CONSTANT tree node
   * @param p node to label
   */
  private static void label_LONG_CONSTANT(AbstractBURS_TreeNode p) {
    p.initCost();
    // rlv: LONG_CONSTANT
    if(BURS.DEBUG) trace(p, 21, 0 + 0, p.getCost(8) /* rlv */);
    if (0 < p.getCost(8) /* rlv */) {
      p.setCost(8 /* rlv */, (char)(0));
      p.writePacked(1, 0xFFFFFFFC, 0x2); // p.rlv = 2
    }
    // any: LONG_CONSTANT
    if(BURS.DEBUG) trace(p, 24, 0 + 0, p.getCost(9) /* any */);
    if (0 < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(0));
      p.writePacked(1, 0xFFFFFFE3, 0x10); // p.any = 4
    }
  }

  /**
   * Labels REGISTER tree node
   * @param p node to label
   */
  private static void label_REGISTER(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: REGISTER
    if(BURS.DEBUG) trace(p, 19, 0 + 0, p.getCost(2) /* r */);
    if (0 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(0));
      p.writePacked(0, 0xFFFF00FF, 0x100); // p.r = 1
      closure_r(p, 0);
    }
  }

  /**
   * Labels OTHER_OPERAND tree node
   * @param p node to label
   */
  private static void label_OTHER_OPERAND(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // any: OTHER_OPERAND(any,any)
    c = STATE(lchild).getCost(9 /* any */) + STATE(rchild).getCost(9 /* any */) + 0;
    if(BURS.DEBUG) trace(p, 53, c + 0, p.getCost(9) /* any */);
    if (c < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(c));
      p.writePacked(1, 0xFFFFFFE3, 0x14); // p.any = 5
    }
  }

  /**
   * Labels NULL tree node
   * @param p node to label
   */
  private static void label_NULL(AbstractBURS_TreeNode p) {
    p.initCost();
    // any: NULL
    if(BURS.DEBUG) trace(p, 22, 0 + 0, p.getCost(9) /* any */);
    if (0 < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(0));
      p.writePacked(1, 0xFFFFFFE3, 0x4); // p.any = 1
    }
  }

  /**
   * Labels BRANCH_TARGET tree node
   * @param p node to label
   */
  private static void label_BRANCH_TARGET(AbstractBURS_TreeNode p) {
    p.initCost();
  }

  /**
   * Labels MATERIALIZE_FP_CONSTANT tree node
   * @param p node to label
   */
  private static void label_MATERIALIZE_FP_CONSTANT(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: MATERIALIZE_FP_CONSTANT(any)
    c = STATE(lchild).getCost(9 /* any */) + 15;
    if(BURS.DEBUG) trace(p, 334, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFF00FF, 0xDD00); // p.r = 221
      closure_r(p, c);
    }
    // float_load: MATERIALIZE_FP_CONSTANT(any)
    c = STATE(lchild).getCost(9 /* any */) + (Binary.getResult(P(p)).isFloat() ? 0 : INFINITE);
    if(BURS.DEBUG) trace(p, 335, c + 0, p.getCost(25) /* float_load */);
    if (c < p.getCost(25) /* float_load */) {
      p.setCost(25 /* float_load */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0xA0000); // p.float_load = 5
    }
    // double_load: MATERIALIZE_FP_CONSTANT(any)
    c = STATE(lchild).getCost(9 /* any */) + (Binary.getResult(P(p)).isDouble() ? 0 : INFINITE);
    if(BURS.DEBUG) trace(p, 336, c + 0, p.getCost(26) /* double_load */);
    if (c < p.getCost(26) /* double_load */) {
      p.setCost(26 /* double_load */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x600000); // p.double_load = 6
    }
  }

  /**
   * Labels CLEAR_FLOATING_POINT_STATE tree node
   * @param p node to label
   */
  private static void label_CLEAR_FLOATING_POINT_STATE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: CLEAR_FLOATING_POINT_STATE
    if(BURS.DEBUG) trace(p, 52, 0 + 0, p.getCost(1) /* stm */);
    if (0 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(0));
      p.writePacked(0, 0xFFFFFF00, 0xB6); // p.stm = 182
    }
  }

  /**
   * Labels PREFETCH tree node
   * @param p node to label
   */
  private static void label_PREFETCH(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // stm: PREFETCH(r)
    c = STATE(lchild).getCost(2 /* r */) + 11;
    if(BURS.DEBUG) trace(p, 226, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x28); // p.stm = 40
    }
  }

  /**
   * Labels PAUSE tree node
   * @param p node to label
   */
  private static void label_PAUSE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: PAUSE
    if(BURS.DEBUG) trace(p, 45, 11 + 0, p.getCost(1) /* stm */);
    if (11 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(11));
      p.writePacked(0, 0xFFFFFF00, 0x2C); // p.stm = 44
    }
  }

  /**
   * Labels CMP_CMOV tree node
   * @param p node to label
   */
  private static void label_CMP_CMOV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (13 + 30);
      if(BURS.DEBUG) trace(p, 374, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3200); // p.r = 50
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (VRL(p) == 0 && CMP_TO_TEST(CondMove.getCond(P(p))) ? (11 + 30):INFINITE);
      if(BURS.DEBUG) trace(p, 477, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3300); // p.r = 51
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + ((VRL(p) == 0 && CondMove.getCond(P(p)).isLESS() && VRRL(p) == -1 && VRRR(p) == 0) || (VRL(p) == 0 && CondMove.getCond(P(p)).isGREATER_EQUAL() && VRRL(p) == 0 && VRRR(p) == -1) ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 256, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3400); // p.r = 52
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + ((VRL(p) == 0 && CondMove.getCond(P(p)).isLESS() && VRRL(p) == -1 && VRRR(p) == 0) || (VRL(p) == 0 && CondMove.getCond(P(p)).isGREATER_EQUAL() && VRRL(p) == 0 && VRRR(p) == -1) ? 18 : INFINITE);
      if(BURS.DEBUG) trace(p, 257, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3500); // p.r = 53
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + ((VRL(p) == 0 && CondMove.getCond(P(p)).isLESS() && VRRL(p) == 0 && VRRR(p) == -1) || (VRL(p) == 0 && CondMove.getCond(P(p)).isGREATER_EQUAL() && VRRL(p) == -1 && VRRR(p) == 0) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 258, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3600); // p.r = 54
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + ((VRL(p) == 0 && CondMove.getCond(P(p)).isLESS() && VRRL(p) == 0 && VRRR(p) == -1) || (VRL(p) == 0 && CondMove.getCond(P(p)).isGREATER_EQUAL() && VRRL(p) == -1 && VRRR(p) == 0) ? 31 : INFINITE);
      if(BURS.DEBUG) trace(p, 259, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3700); // p.r = 55
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load8 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + FITS(CondMove.getVal2(P(p)), 8, (15 + 30));
      if(BURS.DEBUG) trace(p, 478, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3800); // p.r = 56
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(11 /* uload8 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 375, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3900); // p.r = 57
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(11 /* uload8 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 376, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3A00); // p.r = 58
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(21 /* sload16 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + FITS(CondMove.getVal2(P(p)), 8, (15 + 30));
      if(BURS.DEBUG) trace(p, 479, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3B00); // p.r = 59
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 377, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3C00); // p.r = 60
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(10 /* load32 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 378, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3D00); // p.r = 61
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + STATE(rchild.getChild2()).getCost(9 /* any */) + ((VRL(p) == 0 && CondMove.getCond(P(p)).isNOT_EQUAL()) || (VRL(p) == 1 && CondMove.getCond(P(p)).isEQUAL()) ? 30 : INFINITE);
      if(BURS.DEBUG) trace(p, 480, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3E00); // p.r = 62
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + STATE(rchild.getChild2()).getCost(9 /* any */) + ((VRL(p) == 1 && CondMove.getCond(P(p)).isNOT_EQUAL()) || (VRL(p) == 0 && CondMove.getCond(P(p)).isEQUAL()) ? 30 : INFINITE);
      if(BURS.DEBUG) trace(p, 481, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x3F00); // p.r = 63
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + STATE(rchild.getChild2()).getCost(9 /* any */) + ((VRL(p) == 0 || VRL(p) == 1) && EQ_NE(CondMove.getCond(P(p))) ? 30 : INFINITE);
      if(BURS.DEBUG) trace(p, 482, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4000); // p.r = 64
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + STATE(rchild.getChild2()).getCost(9 /* any */) + isZERO(VRL(p), 30);
      if(BURS.DEBUG) trace(p, 483, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4100); // p.r = 65
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + STATE(rchild.getChild2()).getCost(9 /* any */) + isZERO(VRL(p), 30);
      if(BURS.DEBUG) trace(p, 484, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x4200); // p.r = 66
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels FCMP_CMOV tree node
   * @param p node to label
   */
  private static void label_FCMP_CMOV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13*2;
      if(BURS.DEBUG) trace(p, 404, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xDE00); // p.r = 222
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(25 /* float_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 405, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xDF00); // p.r = 223
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(26 /* double_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 406, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE000); // p.r = 224
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(25 /* float_load */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 407, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE100); // p.r = 225
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(26 /* double_load */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 408, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE200); // p.r = 226
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels LCMP_CMOV tree node
   * @param p node to label
   */
  private static void label_LCMP_CMOV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (8*13 + 30);
      if(BURS.DEBUG) trace(p, 384, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0x6E00); // p.r = 110
        closure_r(p, c);
      }
    }
  }

  /**
   * Labels FCMP_FCMOV tree node
   * @param p node to label
   */
  private static void label_FCMP_FCMOV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13*4;
      if(BURS.DEBUG) trace(p, 409, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE300); // p.r = 227
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(25 /* float_load */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 433, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE400); // p.r = 228
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(26 /* double_load */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 434, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE500); // p.r = 229
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(25 /* float_load */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 435, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE600); // p.r = 230
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(26 /* double_load */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 436, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE700); // p.r = 231
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(25 /* float_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (SSE2_CMP_OP(CondMove.getCond(P(p)), true) != null ? 15+13*3 : INFINITE);
      if(BURS.DEBUG) trace(p, 410, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE800); // p.r = 232
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(26 /* double_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (SSE2_CMP_OP(CondMove.getCond(P(p)), false) != null ? 15+13*3 : INFINITE);
      if(BURS.DEBUG) trace(p, 411, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xE900); // p.r = 233
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 554, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xEA00); // p.r = 234
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 555, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xEB00); // p.r = 235
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 558, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xEC00); // p.r = 236
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 559, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xED00); // p.r = 237
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 562, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xEE00); // p.r = 238
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 563, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xEF00); // p.r = 239
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 566, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF000); // p.r = 240
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == FLOAT_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 567, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF100); // p.r = 241
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 556, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF200); // p.r = 242
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 557, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF300); // p.r = 243
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 560, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF400); // p.r = 244
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      rchild.getChild1().getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal1(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 561, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF500); // p.r = 245
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 564, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF600); // p.r = 246
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild1().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_GT_OR_GE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getClearFalseValue(P(p)), Unary.getVal(PRRL(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 565, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF700); // p.r = 247
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 568, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF800); // p.r = 248
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      lchild.getOpcode() == MATERIALIZE_FP_CONSTANT_opcode && 
      lchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == DOUBLE_NEG_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2().getChild1()).getCost(2 /* r */) + (IS_MATERIALIZE_ZERO(PRL(p)) && SSE2_IS_LT_OR_LE(CondMove.getCond(P(p))) && SIMILAR_REGISTERS(CondMove.getVal2(P(p)), CondMove.getTrueValue(P(p)), Unary.getVal(PRRR(p))) ? 11 : INFINITE );
      if(BURS.DEBUG) trace(p, 569, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFF00FF, 0xF900); // p.r = 249
        closure_r(p, c);
      }
    }
  }

  /**
   * Give leaf child corresponding to external rule and child number.
   * e.g. .
   *
   * @param p tree node to get child for
   * @param eruleno external rule number
   * @param kidnumber the child to return
   * @return the requested child
   */
  private static AbstractBURS_TreeNode kids(AbstractBURS_TreeNode p, int eruleno, int kidnumber)  { 
    if (BURS.DEBUG) {
      switch (eruleno) {
      case 18: // load8_16_32: load8
      case 17: // load8_16_32: load16_32
      case 16: // load16_32: load32
      case 15: // load16_32: load16
      case 14: // load16: uload16
      case 13: // load16: sload16
      case 12: // load8: uload8
      case 11: // load8: sload8
      case 10: // address1scaledreg: address1reg
      case 9: // address: address1scaledreg
      case 8: // any: riv
      case 7: // rlv: r
      case 6: // riv: r
      case 5: // szp: szpr
      case 4: // r: szpr
      case 3: // cz: czr
      case 2: // r: czr
      case 1: // stm: r
        if (kidnumber == 0) {
          return p;
        }
        break;
      case 52: // stm: CLEAR_FLOATING_POINT_STATE
      case 51: // r: LONG_MOVE(LONG_CONSTANT)
      case 50: // r: GET_TIME_BASE
      case 49: // stm: RETURN(LONG_CONSTANT)
      case 48: // stm: RETURN(INT_CONSTANT)
      case 47: // stm: RETURN(NULL)
      case 46: // stm: ILLEGAL_INSTRUCTION
      case 45: // stm: PAUSE
      case 44: // stm: FENCE
      case 43: // stm: READ_CEILING
      case 42: // stm: WRITE_FLOOR
      case 41: // stm: GOTO
      case 40: // stm: TRAP
      case 39: // stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
      case 38: // stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
      case 37: // r: GET_CAUGHT_EXCEPTION
      case 36: // stm: IR_PROLOGUE
      case 35: // r: GUARD_COMBINE
      case 34: // r: GUARD_MOVE
      case 33: // stm: NOP
      case 32: // stm: RESOLVE
      case 31: // r: FRAMESIZE
      case 30: // stm: YIELDPOINT_BACKEDGE
      case 29: // stm: YIELDPOINT_EPILOGUE
      case 28: // stm: YIELDPOINT_PROLOGUE
      case 27: // stm: UNINT_END
      case 26: // stm: UNINT_BEGIN
      case 25: // stm: IG_PATCH_POINT
      case 24: // any: LONG_CONSTANT
      case 23: // any: ADDRESS_CONSTANT
      case 22: // any: NULL
      case 21: // rlv: LONG_CONSTANT
      case 20: // riv: INT_CONSTANT
      case 19: // r: REGISTER
        break;
      case 216: // stm: DOUBLE_IFCMP(double_load,r)
      case 215: // stm: DOUBLE_IFCMP(r,double_load)
      case 214: // stm: DOUBLE_IFCMP(r,r)
      case 213: // stm: FLOAT_IFCMP(float_load,r)
      case 212: // stm: FLOAT_IFCMP(r,float_load)
      case 211: // stm: FLOAT_IFCMP(r,r)
      case 210: // float_load: FLOAT_ALOAD(riv,riv)
      case 209: // r: FLOAT_ALOAD(rlv,rlv)
      case 208: // r: FLOAT_ALOAD(riv,r)
      case 207: // r: FLOAT_ALOAD(rlv,riv)
      case 206: // r: FLOAT_ALOAD(riv,riv)
      case 205: // float_load: FLOAT_ALOAD(rlv,riv)
      case 204: // float_load: FLOAT_LOAD(riv,riv)
      case 203: // r: FLOAT_LOAD(rlv,rlv)
      case 202: // r: FLOAT_LOAD(riv,riv)
      case 201: // double_load: DOUBLE_ALOAD(riv,riv)
      case 200: // double_load: DOUBLE_ALOAD(rlv,riv)
      case 199: // r: DOUBLE_ALOAD(rlv,rlv)
      case 198: // r: DOUBLE_ALOAD(riv,r)
      case 197: // double_load: DOUBLE_LOAD(rlv,rlv)
      case 196: // r: DOUBLE_ALOAD(rlv,riv)
      case 195: // r: DOUBLE_ALOAD(riv,riv)
      case 194: // double_load: DOUBLE_LOAD(riv,riv)
      case 193: // r: DOUBLE_LOAD(rlv,rlv)
      case 192: // r: DOUBLE_LOAD(riv,rlv)
      case 191: // r: DOUBLE_LOAD(riv,riv)
      case 190: // r: DOUBLE_REM(r,r)
      case 189: // r: FLOAT_REM(r,r)
      case 188: // r: DOUBLE_DIV(r,double_load)
      case 187: // r: DOUBLE_DIV(r,r)
      case 186: // r: FLOAT_DIV(r,float_load)
      case 185: // r: FLOAT_DIV(r,r)
      case 184: // r: DOUBLE_MUL(double_load,r)
      case 183: // r: DOUBLE_MUL(r,double_load)
      case 182: // r: DOUBLE_MUL(r,r)
      case 181: // r: FLOAT_MUL(float_load,r)
      case 180: // r: FLOAT_MUL(r,float_load)
      case 179: // r: FLOAT_MUL(r,r)
      case 178: // r: DOUBLE_SUB(r,double_load)
      case 177: // r: DOUBLE_SUB(r,r)
      case 176: // r: FLOAT_SUB(r,float_load)
      case 175: // r: FLOAT_SUB(r,r)
      case 174: // r: DOUBLE_ADD(double_load,r)
      case 173: // r: DOUBLE_ADD(r,double_load)
      case 172: // r: DOUBLE_ADD(r,r)
      case 171: // r: FLOAT_ADD(float_load,r)
      case 170: // r: FLOAT_ADD(r,float_load)
      case 169: // r: FLOAT_ADD(r,r)
      case 168: // r: LONG_XOR(load64,rlv)
      case 167: // r: LONG_XOR(r,load64)
      case 166: // r: LONG_XOR(r,rlv)
      case 165: // r: LONG_USHR(rlv,riv)
      case 164: // r: LONG_SUB(load64,rlv)
      case 163: // r: LONG_SUB(rlv,load64)
      case 162: // r: LONG_SUB(rlv,rlv)
      case 161: // r: LONG_SHR(rlv,riv)
      case 160: // r: LONG_SHL(rlv,riv)
      case 159: // r: LONG_OR(load64,rlv)
      case 158: // r: LONG_OR(r,load64)
      case 157: // r: LONG_OR(r,rlv)
      case 156: // r: LONG_MUL(r,rlv)
      case 155: // r: LONG_ALOAD(riv,riv)
      case 154: // r: LONG_LOAD(riv,riv)
      case 153: // stm: LONG_IFCMP(r,rlv)
      case 152: // r: LONG_AND(load64,rlv)
      case 151: // r: LONG_AND(r,load64)
      case 150: // r: LONG_AND(r,rlv)
      case 149: // r: LONG_ADD(load64,rlv)
      case 148: // r: LONG_ADD(r,load64)
      case 147: // r: LONG_ADD(r,rlv)
      case 146: // load64: LONG_ALOAD(riv,riv)
      case 145: // load64: LONG_LOAD(riv,riv)
      case 144: // load32: INT_ALOAD(riv,riv)
      case 143: // load32: INT_LOAD(riv,riv)
      case 142: // uload16: USHORT_ALOAD(riv,riv)
      case 141: // r: USHORT_ALOAD(riv,riv)
      case 140: // uload16: USHORT_LOAD(riv,riv)
      case 139: // r: USHORT_LOAD(riv,riv)
      case 138: // sload16: SHORT_ALOAD(riv,riv)
      case 137: // r: SHORT_ALOAD(riv,riv)
      case 136: // sload16: SHORT_LOAD(riv,riv)
      case 135: // r: SHORT_LOAD(riv,riv)
      case 134: // uload8: UBYTE_ALOAD(riv,riv)
      case 133: // r: UBYTE_ALOAD(riv,riv)
      case 132: // uload8: UBYTE_LOAD(riv,riv)
      case 131: // r: UBYTE_LOAD(riv,riv)
      case 130: // sload8: BYTE_ALOAD(riv,riv)
      case 129: // r: BYTE_ALOAD(riv,riv)
      case 128: // sload8: BYTE_LOAD(riv,riv)
      case 127: // r: BYTE_LOAD(riv,riv)
      case 126: // r: INT_ADD(address1reg,address1scaledreg)
      case 125: // r: INT_ADD(address1scaledreg,address1reg)
      case 124: // r: INT_ADD(r,address1scaledreg)
      case 123: // r: INT_ADD(address1scaledreg,r)
      case 122: // szpr: INT_XOR(load32,riv)
      case 121: // szpr: INT_XOR(r,load32)
      case 120: // szpr: INT_XOR(r,riv)
      case 119: // szpr: INT_USHR(riv,riv)
      case 118: // czr: INT_SUB(load32,riv)
      case 117: // czr: INT_SUB(riv,load32)
      case 116: // r: INT_SUB(load32,r)
      case 115: // r: INT_SUB(riv,r)
      case 114: // czr: INT_SUB(riv,r)
      case 113: // szpr: INT_SHR(riv,riv)
      case 112: // szpr: INT_SHL(riv,riv)
      case 111: // r: UNSIGNED_REM_64_32(rlv,load32)
      case 110: // r: UNSIGNED_REM_64_32(rlv,riv)
      case 109: // r: INT_REM(riv,load32)
      case 108: // r: INT_REM(riv,riv)
      case 107: // szpr: INT_OR(load32,riv)
      case 106: // szpr: INT_OR(r,load32)
      case 105: // szpr: INT_OR(r,riv)
      case 104: // r: INT_MUL(load32,riv)
      case 103: // r: INT_MUL(r,load32)
      case 102: // r: INT_MUL(r,riv)
      case 101: // r: INT_ALOAD(riv,riv)
      case 100: // r: INT_LOAD(address1reg,address1scaledreg)
      case 99: // r: INT_LOAD(address1scaledreg,address1reg)
      case 98: // r: INT_LOAD(address1scaledreg,riv)
      case 97: // r: INT_LOAD(riv,address1scaledreg)
      case 96: // r: INT_LOAD(riv,riv)
      case 95: // stm: INT_IFCMP2(riv,load32)
      case 94: // stm: INT_IFCMP2(load32,riv)
      case 93: // stm: INT_IFCMP2(r,riv)
      case 92: // stm: INT_IFCMP(r,load32)
      case 91: // stm: INT_IFCMP(load32,riv)
      case 90: // stm: INT_IFCMP(r,uload8)
      case 89: // stm: INT_IFCMP(uload8,r)
      case 88: // stm: INT_IFCMP(r,riv)
      case 87: // r: UNSIGNED_DIV_64_32(rlv,load32)
      case 86: // r: UNSIGNED_DIV_64_32(rlv,riv)
      case 85: // r: INT_DIV(riv,load32)
      case 84: // r: INT_DIV(riv,riv)
      case 83: // szp: INT_AND(r,load8_16_32)
      case 82: // szp: INT_AND(load8_16_32,riv)
      case 81: // szpr: INT_AND(load32,riv)
      case 80: // szpr: INT_AND(r,load32)
      case 79: // szp: INT_AND(r,riv)
      case 78: // szpr: INT_AND(r,riv)
      case 77: // czr: INT_ADD(load32,riv)
      case 76: // czr: INT_ADD(r,load32)
      case 75: // r: INT_ADD(r,riv)
      case 74: // czr: INT_ADD(r,riv)
      case 73: // boolcmp: BOOLEAN_CMP_LONG(rlv,rlv)
      case 72: // r: BOOLEAN_CMP_LONG(rlv,rlv)
      case 71: // boolcmp: BOOLEAN_CMP_INT(riv,load32)
      case 70: // r: BOOLEAN_CMP_INT(r,load32)
      case 69: // boolcmp: BOOLEAN_CMP_INT(load32,riv)
      case 68: // r: BOOLEAN_CMP_INT(load32,riv)
      case 67: // boolcmp: BOOLEAN_CMP_INT(r,riv)
      case 66: // r: BOOLEAN_CMP_INT(r,riv)
      case 65: // address: INT_ADD(address1reg,address1scaledreg)
      case 64: // address: INT_ADD(address1scaledreg,address1reg)
      case 63: // address: INT_ADD(address1scaledreg,r)
      case 62: // address: INT_ADD(r,address1scaledreg)
      case 61: // address: INT_ADD(r,r)
      case 60: // stm: YIELDPOINT_OSR(any,any)
      case 59: // r: SYSCALL(r,any)
      case 58: // r: CALL(r,any)
      case 57: // r: LONG_CMP(rlv,rlv)
      case 56: // stm: TRAP_IF(riv,load32)
      case 55: // stm: TRAP_IF(load32,riv)
      case 54: // stm: TRAP_IF(r,r)
      case 53: // any: OTHER_OPERAND(any,any)
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2();
        }
        break;
      case 336: // double_load: MATERIALIZE_FP_CONSTANT(any)
      case 335: // float_load: MATERIALIZE_FP_CONSTANT(any)
      case 334: // r: MATERIALIZE_FP_CONSTANT(any)
      case 333: // double_load: LONG_BITS_AS_DOUBLE(load64)
      case 332: // r: LONG_BITS_AS_DOUBLE(rlv)
      case 331: // float_load: INT_BITS_AS_FLOAT(load32)
      case 330: // r: INT_BITS_AS_FLOAT(riv)
      case 329: // load64: DOUBLE_AS_LONG_BITS(double_load)
      case 328: // r: DOUBLE_AS_LONG_BITS(r)
      case 327: // load32: FLOAT_AS_INT_BITS(float_load)
      case 326: // r: FLOAT_AS_INT_BITS(r)
      case 325: // r: DOUBLE_2LONG(r)
      case 324: // r: DOUBLE_2INT(r)
      case 323: // r: FLOAT_2LONG(r)
      case 322: // r: FLOAT_2INT(r)
      case 321: // r: DOUBLE_2FLOAT(double_load)
      case 320: // r: DOUBLE_2FLOAT(r)
      case 319: // r: FLOAT_2DOUBLE(float_load)
      case 318: // r: FLOAT_2DOUBLE(r)
      case 317: // r: INT_2DOUBLE(load32)
      case 316: // r: INT_2DOUBLE(riv)
      case 315: // r: INT_2FLOAT(load32)
      case 314: // r: INT_2FLOAT(riv)
      case 313: // r: DOUBLE_MOVE(r)
      case 312: // r: FLOAT_MOVE(r)
      case 311: // r: LONG_2DOUBLE(r)
      case 310: // r: LONG_2FLOAT(r)
      case 309: // r: DOUBLE_SQRT(r)
      case 308: // r: FLOAT_SQRT(r)
      case 307: // r: DOUBLE_NEG(r)
      case 306: // r: FLOAT_NEG(r)
      case 305: // r: LONG_NOT(r)
      case 304: // r: LONG_NEG(r)
      case 303: // load64: LONG_MOVE(load64)
      case 302: // r: LONG_MOVE(r)
      case 301: // load32: LONG_2INT(load64)
      case 300: // r: LONG_2INT(load64)
      case 299: // r: LONG_2INT(r)
      case 298: // r: INT_MOVE(address)
      case 297: // r: INT_ADD(address,INT_CONSTANT)
      case 296: // szpr: INT_USHR(riv,INT_CONSTANT)
      case 295: // szpr: INT_SHR(riv,INT_CONSTANT)
      case 294: // r: INT_SHL(r,INT_CONSTANT)
      case 293: // szpr: INT_SHL(r,INT_CONSTANT)
      case 292: // r: INT_NOT(r)
      case 291: // szpr: INT_NEG(r)
      case 290: // load32: INT_MOVE(load32)
      case 289: // load16: INT_MOVE(load16)
      case 288: // uload16: INT_MOVE(uload16)
      case 287: // sload16: INT_MOVE(sload16)
      case 286: // load8: INT_MOVE(load8)
      case 285: // uload8: INT_MOVE(uload8)
      case 284: // sload8: INT_MOVE(sload8)
      case 283: // szp: INT_MOVE(szp)
      case 282: // szpr: INT_MOVE(szpr)
      case 281: // cz: INT_MOVE(cz)
      case 280: // czr: INT_MOVE(czr)
      case 279: // r: INT_MOVE(riv)
      case 278: // r: INT_LOAD(address,INT_CONSTANT)
      case 277: // stm: INT_IFCMP(bittest,INT_CONSTANT)
      case 276: // stm: INT_IFCMP(szp,INT_CONSTANT)
      case 275: // stm: INT_IFCMP(cz,INT_CONSTANT)
      case 274: // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      case 273: // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      case 272: // stm: INT_IFCMP(sload16,INT_CONSTANT)
      case 271: // stm: INT_IFCMP(load8,INT_CONSTANT)
      case 270: // stm: INT_IFCMP(r,INT_CONSTANT)
      case 269: // r: INT_2USHORT(load16_32)
      case 268: // uload16: INT_2USHORT(load16_32)
      case 267: // szpr: INT_2USHORT(r)
      case 266: // sload16: INT_2SHORT(load16_32)
      case 265: // r: INT_2SHORT(load16_32)
      case 264: // r: INT_2SHORT(r)
      case 263: // r: INT_2LONG(load32)
      case 262: // r: INT_2LONG(r)
      case 261: // r: INT_2BYTE(load8_16_32)
      case 260: // r: INT_2BYTE(r)
      case 259: // r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 258: // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 257: // r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 256: // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 255: // r: BOOLEAN_NOT(r)
      case 254: // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 253: // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 252: // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 251: // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 250: // boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      case 249: // r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      case 248: // boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      case 247: // r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      case 246: // boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      case 245: // r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      case 244: // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      case 243: // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 242: // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      case 241: // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 240: // boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 239: // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 238: // r: ADDR_2LONG(load32)
      case 237: // r: ADDR_2LONG(r)
      case 236: // address1scaledreg: INT_ADD(address1scaledreg,INT_CONSTANT)
      case 235: // address1scaledreg: INT_SHL(r,INT_CONSTANT)
      case 234: // address1scaledreg: INT_MOVE(address1scaledreg)
      case 233: // address1reg: INT_ADD(address1reg,INT_CONSTANT)
      case 232: // address1reg: INT_MOVE(address1reg)
      case 231: // address1reg: INT_MOVE(r)
      case 230: // address1reg: INT_ADD(r,INT_CONSTANT)
      case 229: // address: INT_ADD(address1scaledreg,INT_CONSTANT)
      case 228: // address: INT_MOVE(address)
      case 227: // stm: RETURN(r)
      case 226: // stm: PREFETCH(r)
      case 225: // r: INT_AND(load16_32,INT_CONSTANT)
      case 224: // r: INT_2BYTE(load8_16_32)
      case 223: // r: INT_AND(load8_16_32,INT_CONSTANT)
      case 222: // uload8: INT_AND(load8_16_32,INT_CONSTANT)
      case 221: // stm: TRAP_IF(r,LONG_CONSTANT)
      case 220: // stm: TRAP_IF(r,INT_CONSTANT)
      case 219: // stm: SET_CAUGHT_EXCEPTION(r)
      case 218: // stm: NULL_CHECK(riv)
      case 217: // stm: LOWTABLESWITCH(r)
        if (kidnumber == 0) {
          return p.getChild1();
        }
        break;
      case 352: // r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_CONSTANT)
      case 351: // load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      case 350: // load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      case 349: // r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      case 348: // r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      case 347: // r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
      case 346: // r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
      case 345: // szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      case 344: // r: LONG_SHL(INT_2LONG(load64),INT_CONSTANT)
      case 343: // r: LONG_SHL(INT_2LONG(r),INT_CONSTANT)
      case 342: // r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
      case 341: // r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
      case 340: // bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      case 339: // bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
      case 338: // r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
      case 337: // r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        break;
      case 415: // stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
      case 414: // stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
      case 413: // stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
      case 412: // stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
      case 411: // r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
      case 410: // r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
      case 409: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
      case 408: // r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
      case 407: // r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
      case 406: // r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
      case 405: // r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
      case 404: // r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
      case 403: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
      case 402: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      case 401: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
      case 400: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
      case 399: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
      case 398: // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
      case 397: // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
      case 396: // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
      case 395: // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
      case 394: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
      case 393: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      case 392: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
      case 391: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
      case 390: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
      case 389: // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
      case 388: // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
      case 387: // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
      case 386: // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
      case 385: // stm: LONG_STORE(r,OTHER_OPERAND(riv,riv))
      case 384: // r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
      case 383: // stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
      case 382: // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
      case 381: // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,riv))
      case 380: // stm: INT_STORE(riv,OTHER_OPERAND(riv,address1scaledreg))
      case 379: // stm: INT_STORE(riv,OTHER_OPERAND(riv,riv))
      case 378: // r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
      case 377: // r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
      case 376: // r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
      case 375: // r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
      case 374: // r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
      case 373: // stm: BYTE_ASTORE(load8,OTHER_OPERAND(riv,riv))
      case 372: // stm: BYTE_ASTORE(riv,OTHER_OPERAND(riv,riv))
      case 371: // stm: BYTE_STORE(load8,OTHER_OPERAND(riv,riv))
      case 370: // stm: BYTE_STORE(riv,OTHER_OPERAND(riv,riv))
      case 369: // stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
      case 368: // stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
      case 367: // stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
      case 366: // stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      case 365: // stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
      case 364: // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
      case 363: // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      case 362: // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
      case 361: // stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
      case 360: // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      case 359: // stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
      case 358: // stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
      case 357: // stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      case 356: // stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      case 355: // stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      case 354: // stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
      case 353: // stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2();
        }
        break;
      case 418: // stm: LONG_STORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
      case 417: // stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
      case 416: // stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2();
        }
        break;
      case 421: // r: SYSCALL(INT_CONSTANT,any)
      case 420: // r: CALL(INT_CONSTANT,any)
      case 419: // r: CALL(BRANCH_TARGET,any)
        if (kidnumber == 0) {
          return p.getChild2();
        }
        break;
      case 424: // r: SYSCALL(INT_LOAD(riv,riv),any)
      case 423: // r: CALL(LONG_LOAD(rlv,rlv),any)
      case 422: // r: CALL(INT_LOAD(riv,riv),any)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2();
        }
        if (kidnumber == 2) {
          return p.getChild2();
        }
        break;
      case 436: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
      case 435: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
      case 434: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
      case 433: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
      case 432: // r: ATTEMPT_LONG(riv,OTHER_OPERAND(riv,OTHER_OPERAND(rlv,rlv)))
      case 431: // r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      case 430: // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
      case 429: // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
      case 428: // r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      case 427: // r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      case 426: // r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      case 425: // r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild1();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild2().getChild2();
        }
        break;
      case 437: // r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild2();
        }
        break;
      case 438: // r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
        if (kidnumber == 0) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild2();
        }
        break;
      case 448: // stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 447: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 446: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 445: // stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 444: // stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 443: // stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 442: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 441: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 440: // stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 439: // stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild1().getChild2().getChild2().getChild1();
        }
        if (kidnumber == 3) {
          return p.getChild1().getChild2().getChild2().getChild2();
        }
        break;
      case 450: // stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 449: // stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild1().getChild2().getChild2().getChild2();
        }
        break;
      case 452: // stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 451: // stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild1().getChild2().getChild2().getChild2();
        }
        break;
      case 456: // bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      case 455: // bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      case 454: // bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      case 453: // bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild1();
        }
        break;
      case 458: // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
      case 457: // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
        if (kidnumber == 0) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2();
        }
        break;
      case 460: // bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      case 459: // bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1();
        }
        break;
      case 476: // stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 475: // stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 474: // stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 473: // stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 472: // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 471: // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 470: // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 469: // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 468: // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 467: // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 466: // stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 465: // stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 464: // stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 463: // stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 462: // stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 461: // stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild1().getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild1().getChild2();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild2();
        }
        break;
      case 484: // r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
      case 483: // r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
      case 482: // r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
      case 481: // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      case 480: // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      case 479: // r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
      case 478: // r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
      case 477: // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2();
        }
        break;
      case 492: // stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      case 491: // stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      case 490: // stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      case 489: // stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      case 488: // stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      case 487: // stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      case 486: // stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      case 485: // stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2();
        }
        break;
      case 512: // stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 511: // stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 510: // stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 509: // stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 508: // stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 507: // stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 506: // stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 505: // stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 504: // stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 503: // stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 502: // stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 501: // stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 500: // stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 499: // stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 498: // stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 497: // stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 496: // stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 495: // stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 494: // stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 493: // stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild1().getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild1().getChild2();
        }
        if (kidnumber == 2) {
          return p.getChild1().getChild2();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 4) {
          return p.getChild2().getChild2();
        }
        break;
      case 530: // stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 529: // stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 528: // stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 527: // stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 526: // stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 525: // stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 524: // stm: LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 523: // stm: LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 522: // stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 521: // stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 520: // stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 519: // stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 518: // stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 517: // stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 516: // stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 515: // stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 514: // stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 513: // stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild1().getChild2().getChild2();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 4) {
          return p.getChild2().getChild2();
        }
        break;
      case 536: // r: LONG_MUL(INT_2LONG(riv),INT_2LONG(riv))
      case 535: // r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_AND(rlv,LONG_CONSTANT))
      case 534: // r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      case 533: // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      case 532: // r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      case 531: // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        break;
      case 538: // r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      case 537: // r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild2().getChild1().getChild1();
        }
        break;
      case 540: // r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
      case 539: // r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild1().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild2().getChild1();
        }
        break;
      case 547: // r: LONG_USHR(rlv,INT_AND(riv,INT_CONSTANT))
      case 546: // r: LONG_SHR(rlv,INT_AND(riv,INT_CONSTANT))
      case 545: // r: LONG_SHL(rlv,INT_AND(riv,INT_CONSTANT))
      case 544: // szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
      case 543: // stm: INT_STORE(riv,OTHER_OPERAND(address,INT_CONSTANT))
      case 542: // szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
      case 541: // szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        break;
      case 553: // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 552: // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 551: // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 550: // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 549: // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 548: // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild1().getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild1().getChild2();
        }
        if (kidnumber == 2) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 3) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 4) {
          return p.getChild2().getChild2();
        }
        break;
      case 557: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 556: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 555: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      case 554: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild2().getChild1();
        }
        break;
      case 561: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 560: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 559: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      case 558: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild2();
        }
        break;
      case 565: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 564: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 563: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      case 562: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
        if (kidnumber == 0) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild2();
        }
        break;
      case 569: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 568: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 567: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      case 566: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
        if (kidnumber == 0) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1();
        }
        if (kidnumber == 2) {
          return p.getChild2().getChild2().getChild2().getChild1();
        }
        break;
      }
      throw new OptimizingCompilerException("BURS","Bad rule number ",
        Integer.toString(eruleno));
    } else {
      return null;
    }
  }

  /**
   * @param p node whose kids will be marked
   * @param eruleno rule number
   */
  private static void mark_kids(AbstractBURS_TreeNode p, int eruleno)
  {
    byte[] ntsrule = nts[eruleno];
    // 18: load8_16_32: load8
    // 17: load8_16_32: load16_32
    // 16: load16_32: load32
    // 15: load16_32: load16
    // 14: load16: uload16
    // 13: load16: sload16
    // 12: load8: uload8
    // 11: load8: sload8
    // 10: address1scaledreg: address1reg
    // 9: address: address1scaledreg
    // 8: any: riv
    // 7: rlv: r
    // 6: riv: r
    // 5: szp: szpr
    // 4: r: szpr
    // 3: cz: czr
    // 2: r: czr
    // 1: stm: r
    if (eruleno <= 18) {
      if (VM.VerifyAssertions) VM._assert(eruleno > 0);
      mark(p, ntsrule[0]);
    }
    // 52: stm: CLEAR_FLOATING_POINT_STATE
    // 51: r: LONG_MOVE(LONG_CONSTANT)
    // 50: r: GET_TIME_BASE
    // 49: stm: RETURN(LONG_CONSTANT)
    // 48: stm: RETURN(INT_CONSTANT)
    // 47: stm: RETURN(NULL)
    // 46: stm: ILLEGAL_INSTRUCTION
    // 45: stm: PAUSE
    // 44: stm: FENCE
    // 43: stm: READ_CEILING
    // 42: stm: WRITE_FLOOR
    // 41: stm: GOTO
    // 40: stm: TRAP
    // 39: stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
    // 38: stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
    // 37: r: GET_CAUGHT_EXCEPTION
    // 36: stm: IR_PROLOGUE
    // 35: r: GUARD_COMBINE
    // 34: r: GUARD_MOVE
    // 33: stm: NOP
    // 32: stm: RESOLVE
    // 31: r: FRAMESIZE
    // 30: stm: YIELDPOINT_BACKEDGE
    // 29: stm: YIELDPOINT_EPILOGUE
    // 28: stm: YIELDPOINT_PROLOGUE
    // 27: stm: UNINT_END
    // 26: stm: UNINT_BEGIN
    // 25: stm: IG_PATCH_POINT
    // 24: any: LONG_CONSTANT
    // 23: any: ADDRESS_CONSTANT
    // 22: any: NULL
    // 21: rlv: LONG_CONSTANT
    // 20: riv: INT_CONSTANT
    // 19: r: REGISTER
    else if (eruleno <= 52) {
    }
    // 216: stm: DOUBLE_IFCMP(double_load,r)
    // 215: stm: DOUBLE_IFCMP(r,double_load)
    // 214: stm: DOUBLE_IFCMP(r,r)
    // 213: stm: FLOAT_IFCMP(float_load,r)
    // 212: stm: FLOAT_IFCMP(r,float_load)
    // 211: stm: FLOAT_IFCMP(r,r)
    // 210: float_load: FLOAT_ALOAD(riv,riv)
    // 209: r: FLOAT_ALOAD(rlv,rlv)
    // 208: r: FLOAT_ALOAD(riv,r)
    // 207: r: FLOAT_ALOAD(rlv,riv)
    // 206: r: FLOAT_ALOAD(riv,riv)
    // 205: float_load: FLOAT_ALOAD(rlv,riv)
    // 204: float_load: FLOAT_LOAD(riv,riv)
    // 203: r: FLOAT_LOAD(rlv,rlv)
    // 202: r: FLOAT_LOAD(riv,riv)
    // 201: double_load: DOUBLE_ALOAD(riv,riv)
    // 200: double_load: DOUBLE_ALOAD(rlv,riv)
    // 199: r: DOUBLE_ALOAD(rlv,rlv)
    // 198: r: DOUBLE_ALOAD(riv,r)
    // 197: double_load: DOUBLE_LOAD(rlv,rlv)
    // 196: r: DOUBLE_ALOAD(rlv,riv)
    // 195: r: DOUBLE_ALOAD(riv,riv)
    // 194: double_load: DOUBLE_LOAD(riv,riv)
    // 193: r: DOUBLE_LOAD(rlv,rlv)
    // 192: r: DOUBLE_LOAD(riv,rlv)
    // 191: r: DOUBLE_LOAD(riv,riv)
    // 190: r: DOUBLE_REM(r,r)
    // 189: r: FLOAT_REM(r,r)
    // 188: r: DOUBLE_DIV(r,double_load)
    // 187: r: DOUBLE_DIV(r,r)
    // 186: r: FLOAT_DIV(r,float_load)
    // 185: r: FLOAT_DIV(r,r)
    // 184: r: DOUBLE_MUL(double_load,r)
    // 183: r: DOUBLE_MUL(r,double_load)
    // 182: r: DOUBLE_MUL(r,r)
    // 181: r: FLOAT_MUL(float_load,r)
    // 180: r: FLOAT_MUL(r,float_load)
    // 179: r: FLOAT_MUL(r,r)
    // 178: r: DOUBLE_SUB(r,double_load)
    // 177: r: DOUBLE_SUB(r,r)
    // 176: r: FLOAT_SUB(r,float_load)
    // 175: r: FLOAT_SUB(r,r)
    // 174: r: DOUBLE_ADD(double_load,r)
    // 173: r: DOUBLE_ADD(r,double_load)
    // 172: r: DOUBLE_ADD(r,r)
    // 171: r: FLOAT_ADD(float_load,r)
    // 170: r: FLOAT_ADD(r,float_load)
    // 169: r: FLOAT_ADD(r,r)
    // 168: r: LONG_XOR(load64,rlv)
    // 167: r: LONG_XOR(r,load64)
    // 166: r: LONG_XOR(r,rlv)
    // 165: r: LONG_USHR(rlv,riv)
    // 164: r: LONG_SUB(load64,rlv)
    // 163: r: LONG_SUB(rlv,load64)
    // 162: r: LONG_SUB(rlv,rlv)
    // 161: r: LONG_SHR(rlv,riv)
    // 160: r: LONG_SHL(rlv,riv)
    // 159: r: LONG_OR(load64,rlv)
    // 158: r: LONG_OR(r,load64)
    // 157: r: LONG_OR(r,rlv)
    // 156: r: LONG_MUL(r,rlv)
    // 155: r: LONG_ALOAD(riv,riv)
    // 154: r: LONG_LOAD(riv,riv)
    // 153: stm: LONG_IFCMP(r,rlv)
    // 152: r: LONG_AND(load64,rlv)
    // 151: r: LONG_AND(r,load64)
    // 150: r: LONG_AND(r,rlv)
    // 149: r: LONG_ADD(load64,rlv)
    // 148: r: LONG_ADD(r,load64)
    // 147: r: LONG_ADD(r,rlv)
    // 146: load64: LONG_ALOAD(riv,riv)
    // 145: load64: LONG_LOAD(riv,riv)
    // 144: load32: INT_ALOAD(riv,riv)
    // 143: load32: INT_LOAD(riv,riv)
    // 142: uload16: USHORT_ALOAD(riv,riv)
    // 141: r: USHORT_ALOAD(riv,riv)
    // 140: uload16: USHORT_LOAD(riv,riv)
    // 139: r: USHORT_LOAD(riv,riv)
    // 138: sload16: SHORT_ALOAD(riv,riv)
    // 137: r: SHORT_ALOAD(riv,riv)
    // 136: sload16: SHORT_LOAD(riv,riv)
    // 135: r: SHORT_LOAD(riv,riv)
    // 134: uload8: UBYTE_ALOAD(riv,riv)
    // 133: r: UBYTE_ALOAD(riv,riv)
    // 132: uload8: UBYTE_LOAD(riv,riv)
    // 131: r: UBYTE_LOAD(riv,riv)
    // 130: sload8: BYTE_ALOAD(riv,riv)
    // 129: r: BYTE_ALOAD(riv,riv)
    // 128: sload8: BYTE_LOAD(riv,riv)
    // 127: r: BYTE_LOAD(riv,riv)
    // 126: r: INT_ADD(address1reg,address1scaledreg)
    // 125: r: INT_ADD(address1scaledreg,address1reg)
    // 124: r: INT_ADD(r,address1scaledreg)
    // 123: r: INT_ADD(address1scaledreg,r)
    // 122: szpr: INT_XOR(load32,riv)
    // 121: szpr: INT_XOR(r,load32)
    // 120: szpr: INT_XOR(r,riv)
    // 119: szpr: INT_USHR(riv,riv)
    // 118: czr: INT_SUB(load32,riv)
    // 117: czr: INT_SUB(riv,load32)
    // 116: r: INT_SUB(load32,r)
    // 115: r: INT_SUB(riv,r)
    // 114: czr: INT_SUB(riv,r)
    // 113: szpr: INT_SHR(riv,riv)
    // 112: szpr: INT_SHL(riv,riv)
    // 111: r: UNSIGNED_REM_64_32(rlv,load32)
    // 110: r: UNSIGNED_REM_64_32(rlv,riv)
    // 109: r: INT_REM(riv,load32)
    // 108: r: INT_REM(riv,riv)
    // 107: szpr: INT_OR(load32,riv)
    // 106: szpr: INT_OR(r,load32)
    // 105: szpr: INT_OR(r,riv)
    // 104: r: INT_MUL(load32,riv)
    // 103: r: INT_MUL(r,load32)
    // 102: r: INT_MUL(r,riv)
    // 101: r: INT_ALOAD(riv,riv)
    // 100: r: INT_LOAD(address1reg,address1scaledreg)
    // 99: r: INT_LOAD(address1scaledreg,address1reg)
    // 98: r: INT_LOAD(address1scaledreg,riv)
    // 97: r: INT_LOAD(riv,address1scaledreg)
    // 96: r: INT_LOAD(riv,riv)
    // 95: stm: INT_IFCMP2(riv,load32)
    // 94: stm: INT_IFCMP2(load32,riv)
    // 93: stm: INT_IFCMP2(r,riv)
    // 92: stm: INT_IFCMP(r,load32)
    // 91: stm: INT_IFCMP(load32,riv)
    // 90: stm: INT_IFCMP(r,uload8)
    // 89: stm: INT_IFCMP(uload8,r)
    // 88: stm: INT_IFCMP(r,riv)
    // 87: r: UNSIGNED_DIV_64_32(rlv,load32)
    // 86: r: UNSIGNED_DIV_64_32(rlv,riv)
    // 85: r: INT_DIV(riv,load32)
    // 84: r: INT_DIV(riv,riv)
    // 83: szp: INT_AND(r,load8_16_32)
    // 82: szp: INT_AND(load8_16_32,riv)
    // 81: szpr: INT_AND(load32,riv)
    // 80: szpr: INT_AND(r,load32)
    // 79: szp: INT_AND(r,riv)
    // 78: szpr: INT_AND(r,riv)
    // 77: czr: INT_ADD(load32,riv)
    // 76: czr: INT_ADD(r,load32)
    // 75: r: INT_ADD(r,riv)
    // 74: czr: INT_ADD(r,riv)
    // 73: boolcmp: BOOLEAN_CMP_LONG(rlv,rlv)
    // 72: r: BOOLEAN_CMP_LONG(rlv,rlv)
    // 71: boolcmp: BOOLEAN_CMP_INT(riv,load32)
    // 70: r: BOOLEAN_CMP_INT(r,load32)
    // 69: boolcmp: BOOLEAN_CMP_INT(load32,riv)
    // 68: r: BOOLEAN_CMP_INT(load32,riv)
    // 67: boolcmp: BOOLEAN_CMP_INT(r,riv)
    // 66: r: BOOLEAN_CMP_INT(r,riv)
    // 65: address: INT_ADD(address1reg,address1scaledreg)
    // 64: address: INT_ADD(address1scaledreg,address1reg)
    // 63: address: INT_ADD(address1scaledreg,r)
    // 62: address: INT_ADD(r,address1scaledreg)
    // 61: address: INT_ADD(r,r)
    // 60: stm: YIELDPOINT_OSR(any,any)
    // 59: r: SYSCALL(r,any)
    // 58: r: CALL(r,any)
    // 57: r: LONG_CMP(rlv,rlv)
    // 56: stm: TRAP_IF(riv,load32)
    // 55: stm: TRAP_IF(load32,riv)
    // 54: stm: TRAP_IF(r,r)
    // 53: any: OTHER_OPERAND(any,any)
    else if (eruleno <= 216) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2(), ntsrule[1]);
    }
    // 336: double_load: MATERIALIZE_FP_CONSTANT(any)
    // 335: float_load: MATERIALIZE_FP_CONSTANT(any)
    // 334: r: MATERIALIZE_FP_CONSTANT(any)
    // 333: double_load: LONG_BITS_AS_DOUBLE(load64)
    // 332: r: LONG_BITS_AS_DOUBLE(rlv)
    // 331: float_load: INT_BITS_AS_FLOAT(load32)
    // 330: r: INT_BITS_AS_FLOAT(riv)
    // 329: load64: DOUBLE_AS_LONG_BITS(double_load)
    // 328: r: DOUBLE_AS_LONG_BITS(r)
    // 327: load32: FLOAT_AS_INT_BITS(float_load)
    // 326: r: FLOAT_AS_INT_BITS(r)
    // 325: r: DOUBLE_2LONG(r)
    // 324: r: DOUBLE_2INT(r)
    // 323: r: FLOAT_2LONG(r)
    // 322: r: FLOAT_2INT(r)
    // 321: r: DOUBLE_2FLOAT(double_load)
    // 320: r: DOUBLE_2FLOAT(r)
    // 319: r: FLOAT_2DOUBLE(float_load)
    // 318: r: FLOAT_2DOUBLE(r)
    // 317: r: INT_2DOUBLE(load32)
    // 316: r: INT_2DOUBLE(riv)
    // 315: r: INT_2FLOAT(load32)
    // 314: r: INT_2FLOAT(riv)
    // 313: r: DOUBLE_MOVE(r)
    // 312: r: FLOAT_MOVE(r)
    // 311: r: LONG_2DOUBLE(r)
    // 310: r: LONG_2FLOAT(r)
    // 309: r: DOUBLE_SQRT(r)
    // 308: r: FLOAT_SQRT(r)
    // 307: r: DOUBLE_NEG(r)
    // 306: r: FLOAT_NEG(r)
    // 305: r: LONG_NOT(r)
    // 304: r: LONG_NEG(r)
    // 303: load64: LONG_MOVE(load64)
    // 302: r: LONG_MOVE(r)
    // 301: load32: LONG_2INT(load64)
    // 300: r: LONG_2INT(load64)
    // 299: r: LONG_2INT(r)
    // 298: r: INT_MOVE(address)
    // 297: r: INT_ADD(address,INT_CONSTANT)
    // 296: szpr: INT_USHR(riv,INT_CONSTANT)
    // 295: szpr: INT_SHR(riv,INT_CONSTANT)
    // 294: r: INT_SHL(r,INT_CONSTANT)
    // 293: szpr: INT_SHL(r,INT_CONSTANT)
    // 292: r: INT_NOT(r)
    // 291: szpr: INT_NEG(r)
    // 290: load32: INT_MOVE(load32)
    // 289: load16: INT_MOVE(load16)
    // 288: uload16: INT_MOVE(uload16)
    // 287: sload16: INT_MOVE(sload16)
    // 286: load8: INT_MOVE(load8)
    // 285: uload8: INT_MOVE(uload8)
    // 284: sload8: INT_MOVE(sload8)
    // 283: szp: INT_MOVE(szp)
    // 282: szpr: INT_MOVE(szpr)
    // 281: cz: INT_MOVE(cz)
    // 280: czr: INT_MOVE(czr)
    // 279: r: INT_MOVE(riv)
    // 278: r: INT_LOAD(address,INT_CONSTANT)
    // 277: stm: INT_IFCMP(bittest,INT_CONSTANT)
    // 276: stm: INT_IFCMP(szp,INT_CONSTANT)
    // 275: stm: INT_IFCMP(cz,INT_CONSTANT)
    // 274: stm: INT_IFCMP(boolcmp,INT_CONSTANT)
    // 273: stm: INT_IFCMP(boolcmp,INT_CONSTANT)
    // 272: stm: INT_IFCMP(sload16,INT_CONSTANT)
    // 271: stm: INT_IFCMP(load8,INT_CONSTANT)
    // 270: stm: INT_IFCMP(r,INT_CONSTANT)
    // 269: r: INT_2USHORT(load16_32)
    // 268: uload16: INT_2USHORT(load16_32)
    // 267: szpr: INT_2USHORT(r)
    // 266: sload16: INT_2SHORT(load16_32)
    // 265: r: INT_2SHORT(load16_32)
    // 264: r: INT_2SHORT(r)
    // 263: r: INT_2LONG(load32)
    // 262: r: INT_2LONG(r)
    // 261: r: INT_2BYTE(load8_16_32)
    // 260: r: INT_2BYTE(r)
    // 259: r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 258: r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 257: r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 256: r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 255: r: BOOLEAN_NOT(r)
    // 254: boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 253: r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 252: boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 251: r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 250: boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
    // 249: r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
    // 248: boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
    // 247: r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
    // 246: boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
    // 245: r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
    // 244: r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    // 243: r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 242: r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    // 241: r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 240: boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 239: r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 238: r: ADDR_2LONG(load32)
    // 237: r: ADDR_2LONG(r)
    // 236: address1scaledreg: INT_ADD(address1scaledreg,INT_CONSTANT)
    // 235: address1scaledreg: INT_SHL(r,INT_CONSTANT)
    // 234: address1scaledreg: INT_MOVE(address1scaledreg)
    // 233: address1reg: INT_ADD(address1reg,INT_CONSTANT)
    // 232: address1reg: INT_MOVE(address1reg)
    // 231: address1reg: INT_MOVE(r)
    // 230: address1reg: INT_ADD(r,INT_CONSTANT)
    // 229: address: INT_ADD(address1scaledreg,INT_CONSTANT)
    // 228: address: INT_MOVE(address)
    // 227: stm: RETURN(r)
    // 226: stm: PREFETCH(r)
    // 225: r: INT_AND(load16_32,INT_CONSTANT)
    // 224: r: INT_2BYTE(load8_16_32)
    // 223: r: INT_AND(load8_16_32,INT_CONSTANT)
    // 222: uload8: INT_AND(load8_16_32,INT_CONSTANT)
    // 221: stm: TRAP_IF(r,LONG_CONSTANT)
    // 220: stm: TRAP_IF(r,INT_CONSTANT)
    // 219: stm: SET_CAUGHT_EXCEPTION(r)
    // 218: stm: NULL_CHECK(riv)
    // 217: stm: LOWTABLESWITCH(r)
    else if (eruleno <= 336) {
      mark(p.getChild1(), ntsrule[0]);
    }
    // 352: r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_CONSTANT)
    // 351: load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
    // 350: load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
    // 349: r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
    // 348: r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
    // 347: r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
    // 346: r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
    // 345: szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
    // 344: r: LONG_SHL(INT_2LONG(load64),INT_CONSTANT)
    // 343: r: LONG_SHL(INT_2LONG(r),INT_CONSTANT)
    // 342: r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
    // 341: r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
    // 340: bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
    // 339: bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
    // 338: r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
    // 337: r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
    else if (eruleno <= 352) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
    }
    // 415: stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
    // 414: stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
    // 413: stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
    // 412: stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
    // 411: r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
    // 410: r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
    // 409: r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
    // 408: r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
    // 407: r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
    // 406: r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
    // 405: r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
    // 404: r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
    // 403: stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
    // 402: stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
    // 401: stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
    // 400: stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
    // 399: stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
    // 398: stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
    // 397: stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
    // 396: stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
    // 395: stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
    // 394: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
    // 393: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
    // 392: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
    // 391: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
    // 390: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
    // 389: stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
    // 388: stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
    // 387: stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
    // 386: stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
    // 385: stm: LONG_STORE(r,OTHER_OPERAND(riv,riv))
    // 384: r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
    // 383: stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
    // 382: stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
    // 381: stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,riv))
    // 380: stm: INT_STORE(riv,OTHER_OPERAND(riv,address1scaledreg))
    // 379: stm: INT_STORE(riv,OTHER_OPERAND(riv,riv))
    // 378: r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
    // 377: r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
    // 376: r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
    // 375: r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
    // 374: r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
    // 373: stm: BYTE_ASTORE(load8,OTHER_OPERAND(riv,riv))
    // 372: stm: BYTE_ASTORE(riv,OTHER_OPERAND(riv,riv))
    // 371: stm: BYTE_STORE(load8,OTHER_OPERAND(riv,riv))
    // 370: stm: BYTE_STORE(riv,OTHER_OPERAND(riv,riv))
    // 369: stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
    // 368: stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
    // 367: stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
    // 366: stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
    // 365: stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
    // 364: stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
    // 363: stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
    // 362: stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
    // 361: stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
    // 360: stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
    // 359: stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
    // 358: stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
    // 357: stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
    // 356: stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
    // 355: stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
    // 354: stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
    // 353: stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
    else if (eruleno <= 415) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2(), ntsrule[2]);
    }
    // 418: stm: LONG_STORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
    // 417: stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
    // 416: stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
    else if (eruleno <= 418) {
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2(), ntsrule[1]);
    }
    // 421: r: SYSCALL(INT_CONSTANT,any)
    // 420: r: CALL(INT_CONSTANT,any)
    // 419: r: CALL(BRANCH_TARGET,any)
    else if (eruleno <= 421) {
      mark(p.getChild2(), ntsrule[0]);
    }
    // 424: r: SYSCALL(INT_LOAD(riv,riv),any)
    // 423: r: CALL(LONG_LOAD(rlv,rlv),any)
    // 422: r: CALL(INT_LOAD(riv,riv),any)
    else if (eruleno <= 424) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild2(), ntsrule[2]);
    }
    // 436: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
    // 435: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
    // 434: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
    // 433: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
    // 432: r: ATTEMPT_LONG(riv,OTHER_OPERAND(riv,OTHER_OPERAND(rlv,rlv)))
    // 431: r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
    // 430: r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
    // 429: r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
    // 428: r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
    // 427: r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
    // 426: r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
    // 425: r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
    else if (eruleno <= 436) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[3]);
    }
    // 437: r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
    else if (eruleno <= 437) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 438: r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
    else if (eruleno <= 438) {
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 448: stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 447: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 446: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 445: stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 444: stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 443: stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 442: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 441: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 440: stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 439: stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    else if (eruleno <= 448) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild1().getChild2().getChild2().getChild2(), ntsrule[3]);
    }
    // 450: stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 449: stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    else if (eruleno <= 450) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 452: stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 451: stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    else if (eruleno <= 452) {
      mark(p.getChild1().getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 456: bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    // 455: bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    // 454: bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    // 453: bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    else if (eruleno <= 456) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
    }
    // 458: bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
    // 457: bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
    else if (eruleno <= 458) {
      mark(p.getChild1().getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2(), ntsrule[1]);
    }
    // 460: bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
    // 459: bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
    else if (eruleno <= 460) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
    }
    // 476: stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 475: stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 474: stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 473: stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 472: stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 471: stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 470: stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 469: stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 468: stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 467: stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 466: stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 465: stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 464: stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 463: stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 462: stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 461: stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 476) {
      mark(p.getChild1().getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2(), ntsrule[3]);
    }
    // 484: r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
    // 483: r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
    // 482: r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
    // 481: r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
    // 480: r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
    // 479: r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
    // 478: r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
    // 477: r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
    else if (eruleno <= 484) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2(), ntsrule[1]);
    }
    // 492: stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
    // 491: stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
    // 490: stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
    // 489: stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
    // 488: stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
    // 487: stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
    // 486: stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
    // 485: stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 492) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2(), ntsrule[2]);
    }
    // 512: stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 511: stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 510: stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 509: stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 508: stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 507: stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 506: stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 505: stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 504: stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 503: stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 502: stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 501: stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 500: stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 499: stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 498: stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 497: stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 496: stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 495: stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 494: stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 493: stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 512) {
      mark(p.getChild1().getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild1().getChild2(), ntsrule[2]);
      mark(p.getChild2().getChild1(), ntsrule[3]);
      mark(p.getChild2().getChild2(), ntsrule[4]);
    }
    // 530: stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 529: stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 528: stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 527: stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 526: stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 525: stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 524: stm: LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 523: stm: LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 522: stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 521: stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 520: stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 519: stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 518: stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 517: stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 516: stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 515: stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 514: stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 513: stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 530) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2(), ntsrule[2]);
      mark(p.getChild2().getChild1(), ntsrule[3]);
      mark(p.getChild2().getChild2(), ntsrule[4]);
    }
    // 536: r: LONG_MUL(INT_2LONG(riv),INT_2LONG(riv))
    // 535: r: LONG_MUL(LONG_AND(rlv,LONG_CONSTANT),LONG_AND(rlv,LONG_CONSTANT))
    // 534: r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    // 533: r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    // 532: r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    // 531: r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    else if (eruleno <= 536) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
    }
    // 538: r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    // 537: r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    else if (eruleno <= 538) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2().getChild1().getChild1(), ntsrule[3]);
    }
    // 540: r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
    // 539: r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
    else if (eruleno <= 540) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[3]);
    }
    // 547: r: LONG_USHR(rlv,INT_AND(riv,INT_CONSTANT))
    // 546: r: LONG_SHR(rlv,INT_AND(riv,INT_CONSTANT))
    // 545: r: LONG_SHL(rlv,INT_AND(riv,INT_CONSTANT))
    // 544: szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
    // 543: stm: INT_STORE(riv,OTHER_OPERAND(address,INT_CONSTANT))
    // 542: szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
    // 541: szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
    else if (eruleno <= 547) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
    }
    // 553: stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 552: stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 551: stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 550: stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 549: stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 548: stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 553) {
      mark(p.getChild1().getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild1(), ntsrule[3]);
      mark(p.getChild2().getChild2(), ntsrule[4]);
    }
    // 557: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 556: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 555: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
    // 554: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
    else if (eruleno <= 557) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2().getChild1(), ntsrule[2]);
    }
    // 561: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 560: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 559: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
    // 558: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
    else if (eruleno <= 561) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 565: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 564: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 563: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
    // 562: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
    else if (eruleno <= 565) {
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 569: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 568: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 567: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
    // 566: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
    else {
      if (VM.VerifyAssertions) VM._assert(eruleno <= 569);
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2().getChild1(), ntsrule[2]);
    }
  }

  /**
   * For each BURS rule (the number of which provides the index) give its flags byte
   */
  private static final byte[] action={
    0,
    NOFLAGS, // 1 - stm:	r
    NOFLAGS, // 2 - r:	REGISTER
    NOFLAGS, // 3 - r:	czr
    NOFLAGS, // 4 - cz:	czr
    NOFLAGS, // 5 - r:	szpr
    NOFLAGS, // 6 - szp:	szpr
    NOFLAGS, // 7 - riv:	r
    NOFLAGS, // 8 - riv:	INT_CONSTANT
    NOFLAGS, // 9 - rlv:	r
    NOFLAGS, // 10 - rlv:	LONG_CONSTANT
    NOFLAGS, // 11 - any:	NULL
    NOFLAGS, // 12 - any:	riv
    NOFLAGS, // 13 - any:	ADDRESS_CONSTANT
    NOFLAGS, // 14 - any:	LONG_CONSTANT
    NOFLAGS, // 15 - any:	OTHER_OPERAND(any, any)
    EMIT_INSTRUCTION, // 16 - stm:	IG_PATCH_POINT
    EMIT_INSTRUCTION, // 17 - stm:	UNINT_BEGIN
    EMIT_INSTRUCTION, // 18 - stm:	UNINT_END
    EMIT_INSTRUCTION, // 19 - stm:	YIELDPOINT_PROLOGUE
    EMIT_INSTRUCTION, // 20 - stm:	YIELDPOINT_EPILOGUE
    EMIT_INSTRUCTION, // 21 - stm:	YIELDPOINT_BACKEDGE
    EMIT_INSTRUCTION, // 22 - r: FRAMESIZE
    EMIT_INSTRUCTION, // 23 - stm:	LOWTABLESWITCH(r)
    EMIT_INSTRUCTION, // 24 - stm:	RESOLVE
    NOFLAGS, // 25 - stm:	NOP
    EMIT_INSTRUCTION, // 26 - r:	GUARD_MOVE
    EMIT_INSTRUCTION, // 27 - r:	GUARD_COMBINE
    EMIT_INSTRUCTION, // 28 - stm:	NULL_CHECK(riv)
    EMIT_INSTRUCTION, // 29 - stm:	IR_PROLOGUE
    EMIT_INSTRUCTION, // 30 - r:	GET_CAUGHT_EXCEPTION
    EMIT_INSTRUCTION, // 31 - stm:	SET_CAUGHT_EXCEPTION(r)
    EMIT_INSTRUCTION, // 32 - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
    EMIT_INSTRUCTION, // 33 - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
    EMIT_INSTRUCTION, // 34 - stm:	TRAP
    EMIT_INSTRUCTION, // 35 - stm:	TRAP_IF(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 36 - stm:	TRAP_IF(r, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 37 - stm:	TRAP_IF(r, r)
    EMIT_INSTRUCTION, // 38 - stm:	TRAP_IF(load32, riv)
    EMIT_INSTRUCTION, // 39 - stm:	TRAP_IF(riv, load32)
    EMIT_INSTRUCTION, // 40 - uload8:	INT_AND(load8_16_32, INT_CONSTANT)
    EMIT_INSTRUCTION, // 41 - r:	INT_AND(load8_16_32, INT_CONSTANT)
    EMIT_INSTRUCTION, // 42 - r:	INT_2BYTE(load8_16_32)
    EMIT_INSTRUCTION, // 43 - r:	INT_USHR(INT_SHL(load8_16_32, INT_CONSTANT), INT_CONSTANT)
    EMIT_INSTRUCTION, // 44 - r:	INT_AND(load16_32, INT_CONSTANT)
    EMIT_INSTRUCTION, // 45 - r:	INT_USHR(INT_SHL(load16_32, INT_CONSTANT), INT_CONSTANT)
    EMIT_INSTRUCTION, // 46 - stm:	SHORT_STORE(riv, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 47 - stm:	SHORT_STORE(load16, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 48 - stm:    SHORT_STORE(rlv, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 49 - stm:    SHORT_STORE(riv, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 50 - stm:	SHORT_ASTORE(riv, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 51 - stm:	SHORT_ASTORE(load16, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 52 - stm:	SHORT_ASTORE(riv, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 53 - stm:	INT_ASTORE(riv, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 54 - stm:	INT_ASTORE(riv, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 55 - stm:	INT_ASTORE(riv, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 56 - stm:	INT_ASTORE(riv, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 57 - stm:	INT_ASTORE(riv, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 58 - stm:	LONG_ASTORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 59 - stm:	LONG_ASTORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 60 - stm:	LONG_ASTORE(r, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 61 - stm:	LONG_ASTORE(LONG_CONSTANT, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 62 - stm:	LONG_ASTORE(LONG_CONSTANT, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 63 - r:	LONG_CMP(rlv,rlv)
    EMIT_INSTRUCTION, // 64 - stm:	GOTO
    EMIT_INSTRUCTION, // 65 - stm:	PREFETCH(r)
    EMIT_INSTRUCTION, // 66 - stm:	WRITE_FLOOR
    EMIT_INSTRUCTION, // 67 - stm:	READ_CEILING
    EMIT_INSTRUCTION, // 68 - stm:	FENCE
    EMIT_INSTRUCTION, // 69 - stm:	PAUSE
    EMIT_INSTRUCTION, // 70 - stm:	ILLEGAL_INSTRUCTION
    EMIT_INSTRUCTION, // 71 - stm:	RETURN(NULL)
    EMIT_INSTRUCTION, // 72 - stm:	RETURN(INT_CONSTANT)
    EMIT_INSTRUCTION, // 73 - stm:	RETURN(r)
    EMIT_INSTRUCTION, // 74 - stm:	RETURN(LONG_CONSTANT)
    EMIT_INSTRUCTION, // 75 - r:	CALL(r, any)
    EMIT_INSTRUCTION, // 76 - r:	CALL(BRANCH_TARGET, any)
    EMIT_INSTRUCTION, // 77 - r:	CALL(INT_LOAD(riv, riv), any)
    EMIT_INSTRUCTION, // 78 - r:	CALL(INT_CONSTANT, any)
    EMIT_INSTRUCTION, // 79 - r:	CALL(LONG_LOAD(rlv, rlv), any)
    EMIT_INSTRUCTION, // 80 - r:	SYSCALL(r, any)
    EMIT_INSTRUCTION, // 81 - r:	SYSCALL(INT_LOAD(riv, riv), any)
    EMIT_INSTRUCTION, // 82 - r:	SYSCALL(INT_CONSTANT, any)
    EMIT_INSTRUCTION, // 83 - r:      GET_TIME_BASE
    EMIT_INSTRUCTION, // 84 - stm:	YIELDPOINT_OSR(any, any)
    NOFLAGS, // 85 - address:	address1scaledreg
    NOFLAGS, // 86 - address:	INT_MOVE(address)
    EMIT_INSTRUCTION, // 87 - address:	INT_ADD(r, r)
    EMIT_INSTRUCTION, // 88 - address:	INT_ADD(r, address1scaledreg)
    EMIT_INSTRUCTION, // 89 - address:	INT_ADD(address1scaledreg, r)
    EMIT_INSTRUCTION, // 90 - address:	INT_ADD(address1scaledreg, INT_CONSTANT)
    EMIT_INSTRUCTION, // 91 - address:	INT_ADD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 92 - address:	INT_ADD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 93 - address1reg:	INT_ADD(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 94 - address1reg:	INT_MOVE(r)
    NOFLAGS, // 95 - address1reg:	INT_MOVE(address1reg)
    EMIT_INSTRUCTION, // 96 - address1reg:	INT_ADD(address1reg, INT_CONSTANT)
    NOFLAGS, // 97 - address1scaledreg:	address1reg
    NOFLAGS, // 98 - address1scaledreg:	INT_MOVE(address1scaledreg)
    EMIT_INSTRUCTION, // 99 - address1scaledreg:	INT_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 100 - address1scaledreg:	INT_ADD(address1scaledreg, INT_CONSTANT)
    EMIT_INSTRUCTION, // 101 - r:	ADDR_2LONG(r)
    EMIT_INSTRUCTION, // 102 - r:	ADDR_2LONG(load32)
    EMIT_INSTRUCTION, // 103 - r:	ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 104 - r:	ATTEMPT_INT(riv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 105 - r:	ATTEMPT_INT(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 106 - r:	ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 107 - r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 108 - r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 109 - r:	ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 110 - r:	ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 111 - r:	ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 112 - stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 113 - stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 114 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 115 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 116 - stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 117 - stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 118 - stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 119 - stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))), INT_CONSTANT)
    EMIT_INSTRUCTION, // 120 - stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 121 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 122 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 123 - stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 124 - stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 125 - stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 126 - r:	ATTEMPT_LONG(riv, OTHER_OPERAND(riv, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 127 - bittest:	INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 128 - bittest:	INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 129 - bittest:	INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
    EMIT_INSTRUCTION, // 130 - bittest:	INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 131 - bittest:	INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 132 - bittest:	INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
    EMIT_INSTRUCTION, // 133 - bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
    EMIT_INSTRUCTION, // 134 - bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)),load32)
    EMIT_INSTRUCTION, // 135 - bittest:	INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 136 - bittest:	INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 137 - r:	BOOLEAN_CMP_INT(r,riv)
    EMIT_INSTRUCTION, // 138 - boolcmp: BOOLEAN_CMP_INT(r,riv)
    EMIT_INSTRUCTION, // 139 - r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 140 - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 141 - r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 142 - r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    EMIT_INSTRUCTION, // 143 - r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 144 - r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    EMIT_INSTRUCTION, // 145 - r:	BOOLEAN_CMP_INT(cz, INT_CONSTANT)
    EMIT_INSTRUCTION, // 146 - boolcmp: BOOLEAN_CMP_INT(cz, INT_CONSTANT)
    EMIT_INSTRUCTION, // 147 - r:	BOOLEAN_CMP_INT(szp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 148 - boolcmp: BOOLEAN_CMP_INT(szp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 149 - r:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
    EMIT_INSTRUCTION, // 150 - boolcmp:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
    EMIT_INSTRUCTION, // 151 - r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    NOFLAGS, // 152 - boolcmp:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 153 - r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 154 - boolcmp:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 155 - r:	BOOLEAN_CMP_INT(load32,riv)
    EMIT_INSTRUCTION, // 156 - boolcmp: BOOLEAN_CMP_INT(load32,riv)
    EMIT_INSTRUCTION, // 157 - r:	BOOLEAN_CMP_INT(r,load32)
    EMIT_INSTRUCTION, // 158 - boolcmp: BOOLEAN_CMP_INT(riv,load32)
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 159 - stm:	BYTE_STORE(boolcmp, OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 160 - stm:	BYTE_ASTORE(boolcmp, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 161 - r:	BOOLEAN_CMP_LONG(rlv,rlv)
    EMIT_INSTRUCTION, // 162 - boolcmp: BOOLEAN_CMP_LONG(rlv,rlv)
    EMIT_INSTRUCTION, // 163 - r:	BOOLEAN_NOT(r)
    EMIT_INSTRUCTION, // 164 - stm:	BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 165 - stm:	BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 166 - stm:    BYTE_STORE(riv, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 167 - stm:    BYTE_STORE(load8, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 168 - stm:    BYTE_ASTORE(riv, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 169 - stm:    BYTE_ASTORE(load8, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 170 - r: CMP_CMOV(r, OTHER_OPERAND(riv, any))
    EMIT_INSTRUCTION, // 171 - r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 172 - r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 173 - r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 174 - r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 175 - r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 176 - r: CMP_CMOV(load8, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 177 - r: CMP_CMOV(uload8, OTHER_OPERAND(riv, any))
    EMIT_INSTRUCTION, // 178 - r: CMP_CMOV(riv, OTHER_OPERAND(uload8, any))
    EMIT_INSTRUCTION, // 179 - r: CMP_CMOV(sload16, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 180 - r: CMP_CMOV(load32, OTHER_OPERAND(riv, any))
    EMIT_INSTRUCTION, // 181 - r: CMP_CMOV(riv, OTHER_OPERAND(load32, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 182 - r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 183 - r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 184 - r: CMP_CMOV(bittest, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 185 - r: CMP_CMOV(cz, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 186 - r: CMP_CMOV(szp, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 187 - r:	INT_2BYTE(r)
    EMIT_INSTRUCTION, // 188 - r:	INT_2BYTE(load8_16_32)
    EMIT_INSTRUCTION, // 189 - stm:	BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 190 - stm:	BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 191 - r:	INT_2LONG(r)
    EMIT_INSTRUCTION, // 192 - r:	INT_2LONG(load32)
    EMIT_INSTRUCTION, // 193 - r:      LONG_AND(INT_2LONG(r), LONG_CONSTANT)
    EMIT_INSTRUCTION, // 194 - r:      LONG_AND(INT_2LONG(load32), LONG_CONSTANT)
    EMIT_INSTRUCTION, // 195 - r:      LONG_SHL(INT_2LONG(r), INT_CONSTANT)
    EMIT_INSTRUCTION, // 196 - r:      LONG_SHL(INT_2LONG(load64), INT_CONSTANT)
    EMIT_INSTRUCTION, // 197 - r:	INT_2SHORT(r)
    EMIT_INSTRUCTION, // 198 - r:	INT_2SHORT(load16_32)
    EMIT_INSTRUCTION, // 199 - sload16:	INT_2SHORT(load16_32)
    EMIT_INSTRUCTION, // 200 - stm:	SHORT_STORE(INT_2SHORT(r), OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION, // 201 - stm:	SHORT_ASTORE(INT_2SHORT(r), OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 202 - szpr:	INT_2USHORT(r)
    EMIT_INSTRUCTION, // 203 - uload16:	INT_2USHORT(load16_32)
    EMIT_INSTRUCTION, // 204 - r:	INT_2USHORT(load16_32)
    EMIT_INSTRUCTION, // 205 - stm:	SHORT_STORE(INT_2USHORT(r), OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION, // 206 - stm:	SHORT_ASTORE(INT_2USHORT(r), OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 207 - czr:	INT_ADD(r, riv)
    EMIT_INSTRUCTION, // 208 - r:	INT_ADD(r, riv)
    EMIT_INSTRUCTION, // 209 - czr:	INT_ADD(r, load32)
    EMIT_INSTRUCTION, // 210 - czr:	INT_ADD(load32, riv)
    EMIT_INSTRUCTION, // 211 - stm:	INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 212 - stm:	INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 213 - stm:	INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 214 - stm:	INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 215 - szpr:	INT_AND(r, riv)
    EMIT_INSTRUCTION, // 216 - szp:	INT_AND(r, riv)
    EMIT_INSTRUCTION, // 217 - szpr:	INT_AND(r, load32)
    EMIT_INSTRUCTION, // 218 - szpr:	INT_AND(load32, riv)
    EMIT_INSTRUCTION, // 219 - szp:	INT_AND(load8_16_32, riv)
    EMIT_INSTRUCTION, // 220 - szp:	INT_AND(r, load8_16_32)
    EMIT_INSTRUCTION, // 221 - stm:	INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 222 - stm:	INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 223 - stm:	INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 224 - stm:	INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 225 - r:	INT_DIV(riv, riv)
    EMIT_INSTRUCTION, // 226 - r:	INT_DIV(riv, load32)
    EMIT_INSTRUCTION, // 227 - r:     UNSIGNED_DIV_64_32(rlv, riv)
    EMIT_INSTRUCTION, // 228 - r:     UNSIGNED_DIV_64_32(rlv, load32)
    EMIT_INSTRUCTION, // 229 - stm:	INT_IFCMP(r,riv)
    EMIT_INSTRUCTION, // 230 - stm:	INT_IFCMP(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 231 - stm:	INT_IFCMP(load8, INT_CONSTANT)
    EMIT_INSTRUCTION, // 232 - stm:	INT_IFCMP(uload8, r)
    EMIT_INSTRUCTION, // 233 - stm:	INT_IFCMP(r, uload8)
    EMIT_INSTRUCTION, // 234 - stm:	INT_IFCMP(sload16, INT_CONSTANT)
    EMIT_INSTRUCTION, // 235 - stm:	INT_IFCMP(load32, riv)
    EMIT_INSTRUCTION, // 236 - stm:	INT_IFCMP(r, load32)
    EMIT_INSTRUCTION, // 237 - stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 238 - stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 239 - stm:	INT_IFCMP(cz, INT_CONSTANT)
    EMIT_INSTRUCTION, // 240 - stm:	INT_IFCMP(szp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 241 - stm:	INT_IFCMP(bittest, INT_CONSTANT)
    EMIT_INSTRUCTION, // 242 - stm:	INT_IFCMP2(r,riv)
    EMIT_INSTRUCTION, // 243 - stm:	INT_IFCMP2(load32,riv)
    EMIT_INSTRUCTION, // 244 - stm:	INT_IFCMP2(riv,load32)
    EMIT_INSTRUCTION, // 245 - r:	INT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 246 - r:	INT_LOAD(riv, address1scaledreg)
    EMIT_INSTRUCTION, // 247 - r:	INT_LOAD(address1scaledreg, riv)
    EMIT_INSTRUCTION, // 248 - r:	INT_LOAD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 249 - r:	INT_LOAD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 250 - r:	INT_LOAD(address, INT_CONSTANT)
    EMIT_INSTRUCTION, // 251 - r:      INT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 252 - r:	INT_MOVE(riv)
    EMIT_INSTRUCTION, // 253 - czr:	INT_MOVE(czr)
    NOFLAGS, // 254 - cz:	INT_MOVE(cz)
    EMIT_INSTRUCTION, // 255 - szpr:	INT_MOVE(szpr)
    NOFLAGS, // 256 - szp:	INT_MOVE(szp)
    NOFLAGS, // 257 - sload8:	INT_MOVE(sload8)
    NOFLAGS, // 258 - uload8:	INT_MOVE(uload8)
    NOFLAGS, // 259 - load8:	INT_MOVE(load8)
    NOFLAGS, // 260 - sload16: INT_MOVE(sload16)
    NOFLAGS, // 261 - uload16: INT_MOVE(uload16)
    NOFLAGS, // 262 - load16:	INT_MOVE(load16)
    NOFLAGS, // 263 - load32:	INT_MOVE(load32)
    EMIT_INSTRUCTION, // 264 - r:	INT_MUL(r, riv)
    EMIT_INSTRUCTION, // 265 - r:	INT_MUL(r, load32)
    EMIT_INSTRUCTION, // 266 - r:	INT_MUL(load32, riv)
    EMIT_INSTRUCTION, // 267 - szpr:	INT_NEG(r)
    EMIT_INSTRUCTION, // 268 - stm:	INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 269 - stm:	INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 270 - r:	INT_NOT(r)
    EMIT_INSTRUCTION, // 271 - stm:	INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 272 - stm:	INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 273 - szpr:	INT_OR(r, riv)
    EMIT_INSTRUCTION, // 274 - szpr:	INT_OR(r, load32)
    EMIT_INSTRUCTION, // 275 - szpr:	INT_OR(load32, riv)
    EMIT_INSTRUCTION, // 276 - stm:	INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 277 - stm:	INT_STORE(INT_OR(r, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 278 - stm:	INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 279 - stm:	INT_ASTORE(INT_OR(r, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 280 - r:	INT_REM(riv, riv)
    EMIT_INSTRUCTION, // 281 - r:	INT_REM(riv, load32)
    EMIT_INSTRUCTION, // 282 - r:     UNSIGNED_REM_64_32(rlv, riv)
    EMIT_INSTRUCTION, // 283 - r:     UNSIGNED_REM_64_32(rlv, load32)
    EMIT_INSTRUCTION, // 284 - r:	INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 285 - r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 286 - r:      INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 287 - r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 288 - r:      INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    EMIT_INSTRUCTION, // 289 - r:      INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
    EMIT_INSTRUCTION, // 290 - r:      INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
    EMIT_INSTRUCTION, // 291 - r:      INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    EMIT_INSTRUCTION, // 292 - szpr:	INT_SHL(riv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 293 - szpr:	INT_SHL(riv, riv)
    EMIT_INSTRUCTION, // 294 - szpr:	INT_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 295 - r:	INT_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 296 - szpr:	INT_SHL(INT_SHR(r, INT_CONSTANT), INT_CONSTANT)
    EMIT_INSTRUCTION, // 297 - stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 298 - stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 299 - stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 300 - stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 301 - szpr:	INT_SHR(riv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 302 - szpr:	INT_SHR(riv, riv)
    EMIT_INSTRUCTION, // 303 - szpr:	INT_SHR(riv, INT_CONSTANT)
    EMIT_INSTRUCTION, // 304 - stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 305 - stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 306 - stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 307 - stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 308 - stm:	INT_STORE(riv, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 309 - stm:	INT_STORE(riv, OTHER_OPERAND(riv, address1scaledreg))
    EMIT_INSTRUCTION, // 310 - stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, riv))
    EMIT_INSTRUCTION, // 311 - stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, address1reg))
    EMIT_INSTRUCTION, // 312 - stm:	INT_STORE(riv, OTHER_OPERAND(address1reg, address1scaledreg))
    EMIT_INSTRUCTION, // 313 - stm:	INT_STORE(riv, OTHER_OPERAND(address, INT_CONSTANT))
    EMIT_INSTRUCTION, // 314 - czr:	INT_SUB(riv, r)
    EMIT_INSTRUCTION, // 315 - r:	INT_SUB(riv, r)
    EMIT_INSTRUCTION, // 316 - r:	INT_SUB(load32, r)
    EMIT_INSTRUCTION, // 317 - czr:	INT_SUB(riv, load32)
    EMIT_INSTRUCTION, // 318 - czr:	INT_SUB(load32, riv)
    EMIT_INSTRUCTION, // 319 - stm:	INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 320 - stm:	INT_STORE(INT_SUB(riv, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 321 - stm:	INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 322 - stm:	INT_ASTORE(INT_SUB(riv, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 323 - szpr:	INT_USHR(riv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 324 - szpr:	INT_USHR(riv, riv)
    EMIT_INSTRUCTION, // 325 - szpr:	INT_USHR(riv, INT_CONSTANT)
    EMIT_INSTRUCTION, // 326 - stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 327 - stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 328 - stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 329 - stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 330 - szpr:	INT_XOR(r, riv)
    EMIT_INSTRUCTION, // 331 - szpr:	INT_XOR(r, load32)
    EMIT_INSTRUCTION, // 332 - szpr:	INT_XOR(load32, riv)
    EMIT_INSTRUCTION, // 333 - stm:	INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 334 - stm:	INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 335 - stm:	INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 336 - stm:	INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 337 - r: LCMP_CMOV(r, OTHER_OPERAND(rlv, any))
    EMIT_INSTRUCTION, // 338 - r:	INT_ADD(address1scaledreg, r)
    EMIT_INSTRUCTION, // 339 - r:	INT_ADD(r, address1scaledreg)
    EMIT_INSTRUCTION, // 340 - r:	INT_ADD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 341 - r:	INT_ADD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 342 - r:	INT_ADD(address, INT_CONSTANT)
    EMIT_INSTRUCTION, // 343 - r:	INT_MOVE(address)
    EMIT_INSTRUCTION, // 344 - r:      BYTE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 345 - sload8:	BYTE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 346 - r:      BYTE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 347 - sload8:	BYTE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 348 - r:      UBYTE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 349 - uload8:	UBYTE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 350 - r:      UBYTE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 351 - uload8:	UBYTE_ALOAD(riv, riv)
    NOFLAGS, // 352 - load8:	sload8
    NOFLAGS, // 353 - load8:	uload8
    EMIT_INSTRUCTION, // 354 - r:      SHORT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 355 - sload16: SHORT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 356 - r:      SHORT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 357 - sload16: SHORT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 358 - r:      USHORT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 359 - uload16: USHORT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 360 - r:      USHORT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 361 - uload16: USHORT_ALOAD(riv, riv)
    NOFLAGS, // 362 - load16:	sload16
    NOFLAGS, // 363 - load16:	uload16
    EMIT_INSTRUCTION, // 364 - load32:	INT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 365 - load32:	INT_ALOAD(riv, riv)
    NOFLAGS, // 366 - load16_32:      load16
    NOFLAGS, // 367 - load16_32:      load32
    NOFLAGS, // 368 - load8_16_32:	load16_32
    NOFLAGS, // 369 - load8_16_32:	load8
    EMIT_INSTRUCTION, // 370 - load64:	LONG_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 371 - load64:	LONG_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 372 - r:	LONG_2INT(r)
    EMIT_INSTRUCTION, // 373 - stm:	INT_STORE(LONG_2INT(r), OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION, // 374 - stm:	INT_ASTORE(LONG_2INT(r), OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 375 - r:	LONG_2INT(load64)
    EMIT_INSTRUCTION, // 376 - load32:      LONG_2INT(load64)
    EMIT_INSTRUCTION, // 377 - r:	LONG_2INT(LONG_USHR(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 378 - r:      LONG_2INT(LONG_SHR(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 379 - r:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 380 - r:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 381 - load32:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 382 - load32:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 383 - r:	LONG_ADD(r, rlv)
    EMIT_INSTRUCTION, // 384 - r:	LONG_ADD(r, load64)
    EMIT_INSTRUCTION, // 385 - r:	LONG_ADD(load64, rlv)
    EMIT_INSTRUCTION, // 386 - stm:	LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 387 - stm:	LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 388 - stm:	LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 389 - stm:	LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 390 - r:	LONG_AND(r, rlv)
    EMIT_INSTRUCTION, // 391 - r:	LONG_AND(r, load64)
    EMIT_INSTRUCTION, // 392 - r:	LONG_AND(load64, rlv)
    EMIT_INSTRUCTION, // 393 - stm:	LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 394 - stm:	LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 395 - stm:	LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 396 - stm:	LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 397 - stm:	LONG_IFCMP(r,rlv)
    EMIT_INSTRUCTION, // 398 - r:	LONG_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 399 - r:      LONG_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 400 - r:	LONG_MOVE(r)
    EMIT_INSTRUCTION, // 401 - r:	LONG_MOVE(LONG_CONSTANT)
    NOFLAGS, // 402 - load64:	LONG_MOVE(load64)
    EMIT_INSTRUCTION, // 403 - r:	LONG_MUL(r, rlv)
    EMIT_INSTRUCTION, // 404 - r:      LONG_MUL(LONG_AND(rlv, LONG_CONSTANT), LONG_AND(rlv, LONG_CONSTANT))
    EMIT_INSTRUCTION, // 405 - r:      LONG_MUL(LONG_AND(rlv, LONG_CONSTANT), LONG_CONSTANT)
    EMIT_INSTRUCTION, // 406 - r:      LONG_MUL(INT_2LONG(riv), INT_2LONG(riv))
    EMIT_INSTRUCTION, // 407 - r:	LONG_NEG(r)
    EMIT_INSTRUCTION, // 408 - stm:	LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 409 - stm:	LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 410 - r:	LONG_NOT(r)
    EMIT_INSTRUCTION, // 411 - stm:	LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 412 - stm:	LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 413 - r:	LONG_OR(r, rlv)
    EMIT_INSTRUCTION, // 414 - r:	LONG_OR(r, load64)
    EMIT_INSTRUCTION, // 415 - r:	LONG_OR(load64, rlv)
    EMIT_INSTRUCTION, // 416 - stm:	LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 417 - stm:	LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 418 - stm:	LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 419 - stm:	LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 420 - r:	LONG_SHL(rlv, riv)
    EMIT_INSTRUCTION, // 421 - r:	LONG_SHL(rlv, INT_AND(riv, INT_CONSTANT))
    EMIT_INSTRUCTION, // 422 - r:	LONG_SHR(rlv, riv)
    EMIT_INSTRUCTION, // 423 - r:	LONG_SHR(rlv, INT_AND(riv, INT_CONSTANT))
    EMIT_INSTRUCTION, // 424 - stm:	LONG_STORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 425 - stm:	LONG_STORE(LONG_CONSTANT, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 426 - r:	LONG_SUB(rlv, rlv)
    EMIT_INSTRUCTION, // 427 - r:	LONG_SUB(rlv, load64)
    EMIT_INSTRUCTION, // 428 - r:	LONG_SUB(load64, rlv)
    EMIT_INSTRUCTION, // 429 - stm:	LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 430 - stm:	LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 431 - r:	LONG_USHR(rlv, riv)
    EMIT_INSTRUCTION, // 432 - r:	LONG_USHR(rlv, INT_AND(riv, INT_CONSTANT))
    EMIT_INSTRUCTION, // 433 - r:	LONG_XOR(r, rlv)
    EMIT_INSTRUCTION, // 434 - r:	LONG_XOR(r, load64)
    EMIT_INSTRUCTION, // 435 - r:	LONG_XOR(load64, rlv)
    EMIT_INSTRUCTION, // 436 - stm:	LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 437 - stm:	LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 438 - stm:	LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 439 - stm:	LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 440 - r: FLOAT_ADD(r, r)
    EMIT_INSTRUCTION, // 441 - r: FLOAT_ADD(r, float_load)
    EMIT_INSTRUCTION, // 442 - r: FLOAT_ADD(float_load,r)
    EMIT_INSTRUCTION, // 443 - r: DOUBLE_ADD(r, r)
    EMIT_INSTRUCTION, // 444 - r: DOUBLE_ADD(r, double_load)
    EMIT_INSTRUCTION, // 445 - r: DOUBLE_ADD(double_load,r)
    EMIT_INSTRUCTION, // 446 - r: FLOAT_SUB(r, r)
    EMIT_INSTRUCTION, // 447 - r: FLOAT_SUB(r, float_load)
    EMIT_INSTRUCTION, // 448 - r: DOUBLE_SUB(r, r)
    EMIT_INSTRUCTION, // 449 - r: DOUBLE_SUB(r, double_load)
    EMIT_INSTRUCTION, // 450 - r: FLOAT_MUL(r, r)
    EMIT_INSTRUCTION, // 451 - r: FLOAT_MUL(r, float_load)
    EMIT_INSTRUCTION, // 452 - r: FLOAT_MUL(float_load, r)
    EMIT_INSTRUCTION, // 453 - r: DOUBLE_MUL(r, r)
    EMIT_INSTRUCTION, // 454 - r: DOUBLE_MUL(r, double_load)
    EMIT_INSTRUCTION, // 455 - r: DOUBLE_MUL(double_load, r)
    EMIT_INSTRUCTION, // 456 - r: FLOAT_DIV(r, r)
    EMIT_INSTRUCTION, // 457 - r: FLOAT_DIV(r, float_load)
    EMIT_INSTRUCTION, // 458 - r: DOUBLE_DIV(r, r)
    EMIT_INSTRUCTION, // 459 - r: DOUBLE_DIV(r, double_load)
    EMIT_INSTRUCTION, // 460 - r: FLOAT_NEG(r)
    EMIT_INSTRUCTION, // 461 - r: DOUBLE_NEG(r)
    EMIT_INSTRUCTION, // 462 - r: FLOAT_SQRT(r)
    EMIT_INSTRUCTION, // 463 - r: DOUBLE_SQRT(r)
    EMIT_INSTRUCTION, // 464 - r: FLOAT_REM(r, r)
    EMIT_INSTRUCTION, // 465 - r: DOUBLE_REM(r, r)
    EMIT_INSTRUCTION, // 466 - r: LONG_2FLOAT(r)
    EMIT_INSTRUCTION, // 467 - r: LONG_2DOUBLE(r)
    EMIT_INSTRUCTION, // 468 - r: FLOAT_MOVE(r)
    EMIT_INSTRUCTION, // 469 - r: DOUBLE_MOVE(r)
    EMIT_INSTRUCTION, // 470 - r: DOUBLE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 471 - r: DOUBLE_LOAD(riv, rlv)
    EMIT_INSTRUCTION, // 472 - r: DOUBLE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 473 - double_load: DOUBLE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 474 - r: DOUBLE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 475 - r: DOUBLE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 476 - double_load: DOUBLE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 477 - r: DOUBLE_ALOAD(riv, r)
    EMIT_INSTRUCTION, // 478 - r: DOUBLE_ALOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 479 - double_load: DOUBLE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 480 - double_load: DOUBLE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 481 - r: FLOAT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 482 - r: FLOAT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 483 - float_load: FLOAT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 484 - float_load: FLOAT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 485 - r: FLOAT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 486 - r: FLOAT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 487 - r: FLOAT_ALOAD(riv, r)
    EMIT_INSTRUCTION, // 488 - r: FLOAT_ALOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 489 - float_load: FLOAT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 490 - stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 491 - stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 492 - stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 493 - stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 494 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 495 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 496 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 497 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 498 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 499 - stm: FLOAT_STORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 500 - stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 501 - stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 502 - stm: FLOAT_STORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 503 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 504 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 505 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 506 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 507 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 508 - r: INT_2FLOAT(riv)
    EMIT_INSTRUCTION, // 509 - r: INT_2FLOAT(load32)
    EMIT_INSTRUCTION, // 510 - r: INT_2DOUBLE(riv)
    EMIT_INSTRUCTION, // 511 - r: INT_2DOUBLE(load32)
    EMIT_INSTRUCTION, // 512 - r: FLOAT_2DOUBLE(r)
    EMIT_INSTRUCTION, // 513 - r: FLOAT_2DOUBLE(float_load)
    EMIT_INSTRUCTION, // 514 - r: DOUBLE_2FLOAT(r)
    EMIT_INSTRUCTION, // 515 - r: DOUBLE_2FLOAT(double_load)
    EMIT_INSTRUCTION, // 516 - r: FLOAT_2INT(r)
    EMIT_INSTRUCTION, // 517 - r: FLOAT_2LONG(r)
    EMIT_INSTRUCTION, // 518 - r: DOUBLE_2INT(r)
    EMIT_INSTRUCTION, // 519 - r: DOUBLE_2LONG(r)
    EMIT_INSTRUCTION, // 520 - r: FLOAT_AS_INT_BITS(r)
    NOFLAGS, // 521 - load32: FLOAT_AS_INT_BITS(float_load)
    EMIT_INSTRUCTION, // 522 - r: DOUBLE_AS_LONG_BITS(r)
    NOFLAGS, // 523 - load64: DOUBLE_AS_LONG_BITS(double_load)
    EMIT_INSTRUCTION, // 524 - r: INT_BITS_AS_FLOAT(riv)
    NOFLAGS, // 525 - float_load: INT_BITS_AS_FLOAT(load32)
    EMIT_INSTRUCTION, // 526 - r: LONG_BITS_AS_DOUBLE(rlv)
    NOFLAGS, // 527 - double_load: LONG_BITS_AS_DOUBLE(load64)
    EMIT_INSTRUCTION, // 528 - r: MATERIALIZE_FP_CONSTANT(any)
    EMIT_INSTRUCTION, // 529 - float_load: MATERIALIZE_FP_CONSTANT(any)
    EMIT_INSTRUCTION, // 530 - double_load: MATERIALIZE_FP_CONSTANT(any)
    EMIT_INSTRUCTION, // 531 - stm: CLEAR_FLOATING_POINT_STATE
    EMIT_INSTRUCTION, // 532 - stm: FLOAT_IFCMP(r,r)
    EMIT_INSTRUCTION, // 533 - stm: FLOAT_IFCMP(r,float_load)
    EMIT_INSTRUCTION, // 534 - stm: FLOAT_IFCMP(float_load,r)
    EMIT_INSTRUCTION, // 535 - stm: DOUBLE_IFCMP(r,r)
    EMIT_INSTRUCTION, // 536 - stm: DOUBLE_IFCMP(r,double_load)
    EMIT_INSTRUCTION, // 537 - stm: DOUBLE_IFCMP(double_load,r)
    EMIT_INSTRUCTION, // 538 - r: FCMP_CMOV(r, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 539 - r: FCMP_CMOV(r, OTHER_OPERAND(float_load, any))
    EMIT_INSTRUCTION, // 540 - r: FCMP_CMOV(r, OTHER_OPERAND(double_load, any))
    EMIT_INSTRUCTION, // 541 - r: FCMP_CMOV(float_load, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 542 - r: FCMP_CMOV(double_load, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 543 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 544 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, float_load)))
    EMIT_INSTRUCTION, // 545 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, double_load)))
    EMIT_INSTRUCTION, // 546 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(float_load, r)))
    EMIT_INSTRUCTION, // 547 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(double_load, r)))
    EMIT_INSTRUCTION, // 548 - r: FCMP_FCMOV(r, OTHER_OPERAND(float_load, any))
    EMIT_INSTRUCTION, // 549 - r: FCMP_FCMOV(r, OTHER_OPERAND(double_load, any))
    EMIT_INSTRUCTION, // 550 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 551 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 552 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 553 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 554 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 555 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 556 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 557 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 558 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 559 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 560 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 561 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 562 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 563 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 564 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 565 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 566 - stm: LONG_ASTORE(load64, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 567 - stm: LONG_ASTORE(load64, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 568 - stm: LONG_STORE(load64, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 569 - stm: LONG_STORE(load64, OTHER_OPERAND(rlv, riv))
  };

  /**
   * Gets the action flags (such as EMIT_INSTRUCTION) associated with the given
   * rule number.
   *
   * @param ruleno the rule number we want the action flags for
   * @return the action byte for the rule
   */
  @Pure
  public static byte action(int ruleno) {
    return action[unsortedErnMap[ruleno]];
  }

  /**
   * Decode the target non-terminal and minimal cost covering statement
   * into the rule that produces the non-terminal
   *
   * @param goalnt the non-terminal that we wish to produce.
   * @param stateNT the state encoding the non-terminals associated associated
   *        with covering a tree with minimal cost (computed by at compile time
   *        by jburg).
   * @return the rule number
   */
   @Pure
   public static char decode(int goalnt, int stateNT) {
     return decode[goalnt][stateNT];
   }


  /**
   * Emit code for rule number 16:
   * stm:	IG_PATCH_POINT
   * @param p BURS node to apply the rule to
   */
  private void code16(AbstractBURS_TreeNode p) {
    EMIT(InlineGuard.mutate(P(p), IG_PATCH_POINT, null, null, null, InlineGuard.getTarget(P(p)), InlineGuard.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 17:
   * stm:	UNINT_BEGIN
   * @param p BURS node to apply the rule to
   */
  private void code17(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 18:
   * stm:	UNINT_END
   * @param p BURS node to apply the rule to
   */
  private void code18(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 19:
   * stm:	YIELDPOINT_PROLOGUE
   * @param p BURS node to apply the rule to
   */
  private void code19(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 20:
   * stm:	YIELDPOINT_EPILOGUE
   * @param p BURS node to apply the rule to
   */
  private void code20(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 21:
   * stm:	YIELDPOINT_BACKEDGE
   * @param p BURS node to apply the rule to
   */
  private void code21(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 22:
   * r: FRAMESIZE
   * @param p BURS node to apply the rule to
   */
  private void code22(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Nullary.getClearResult(P(p)), new UnknownConstantOperand()));
  }

  /**
   * Emit code for rule number 23:
   * stm:	LOWTABLESWITCH(r)
   * @param p BURS node to apply the rule to
   */
  private void code23(AbstractBURS_TreeNode p) {
    LOWTABLESWITCH(P(p));
  }

  /**
   * Emit code for rule number 24:
   * stm:	RESOLVE
   * @param p BURS node to apply the rule to
   */
  private void code24(AbstractBURS_TreeNode p) {
    RESOLVE(P(p));
  }

  /**
   * Emit code for rule number 26:
   * r:	GUARD_MOVE
   * @param p BURS node to apply the rule to
   */
  private void code26(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 27:
   * r:	GUARD_COMBINE
   * @param p BURS node to apply the rule to
   */
  private void code27(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 28:
   * stm:	NULL_CHECK(riv)
   * @param p BURS node to apply the rule to
   */
  private void code28(AbstractBURS_TreeNode p) {
    EMIT(P(p));
  }

  /**
   * Emit code for rule number 29:
   * stm:	IR_PROLOGUE
   * @param p BURS node to apply the rule to
   */
  private void code29(AbstractBURS_TreeNode p) {
    PROLOGUE(P(p));
  }

  /**
   * Emit code for rule number 30:
   * r:	GET_CAUGHT_EXCEPTION
   * @param p BURS node to apply the rule to
   */
  private void code30(AbstractBURS_TreeNode p) {
    GET_EXCEPTION_OBJECT(P(p));
  }

  /**
   * Emit code for rule number 31:
   * stm:	SET_CAUGHT_EXCEPTION(r)
   * @param p BURS node to apply the rule to
   */
  private void code31(AbstractBURS_TreeNode p) {
    SET_EXCEPTION_OBJECT(P(p));
  }

  /**
   * Emit code for rule number 32:
   * stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code32(AbstractBURS_TreeNode p) {
    SET_EXCEPTION_OBJECT(P(p));
  }

  /**
   * Emit code for rule number 33:
   * stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code33(AbstractBURS_TreeNode p) {
    SET_EXCEPTION_OBJECT(P(p));
  }

  /**
   * Emit code for rule number 34:
   * stm:	TRAP
   * @param p BURS node to apply the rule to
   */
  private void code34(AbstractBURS_TreeNode p) {
    EMIT(MIR_Trap.mutate(P(p), IA32_INT, Trap.getGuardResult(P(p)), Trap.getTCode(P(p))));
  }

  /**
   * Emit code for rule number 35:
   * stm:	TRAP_IF(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code35(AbstractBURS_TreeNode p) {
    TRAP_IF_IMM(P(p), false);
  }

  /**
   * Emit code for rule number 36:
   * stm:	TRAP_IF(r, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code36(AbstractBURS_TreeNode p) {
    TRAP_IF_IMM(P(p), true);
  }

  /**
   * Emit code for rule number 37:
   * stm:	TRAP_IF(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code37(AbstractBURS_TreeNode p) {
    EMIT(MIR_TrapIf.mutate(P(p), IA32_TRAPIF, 
                       TrapIf.getGuardResult(P(p)), 
		       TrapIf.getVal1(P(p)), 
		       TrapIf.getVal2(P(p)), 
		       COND(TrapIf.getCond(P(p))), 
		       TrapIf.getTCode(P(p))));
  }

  /**
   * Emit code for rule number 38:
   * stm:	TRAP_IF(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code38(AbstractBURS_TreeNode p) {
    EMIT(MIR_TrapIf.mutate(P(p), IA32_TRAPIF, 
                       TrapIf.getGuardResult(P(p)), 
		       consumeMO(), 
		       TrapIf.getVal2(P(p)), 
		       COND(TrapIf.getCond(P(p))), 
		       TrapIf.getTCode(P(p))));
  }

  /**
   * Emit code for rule number 39:
   * stm:	TRAP_IF(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code39(AbstractBURS_TreeNode p) {
    EMIT(MIR_TrapIf.mutate(P(p), IA32_TRAPIF, 
                       TrapIf.getGuardResult(P(p)), 
		       TrapIf.getVal1(P(p)), 
	               consumeMO(), 
		       COND(TrapIf.getCond(P(p))), 
		       TrapIf.getTCode(P(p))));
  }

  /**
   * Emit code for rule number 40:
   * uload8:	INT_AND(load8_16_32, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code40(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(),1));
  }

  /**
   * Emit code for rule number 41:
   * r:	INT_AND(load8_16_32, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code41(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, Binary.getResult(P(p)), setSize(consumeMO(),1)));
  }

  /**
   * Emit code for rule number 42:
   * r:	INT_2BYTE(load8_16_32)
   * @param p BURS node to apply the rule to
   */
  private void code42(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Unary.getResult(P(p)), setSize(consumeMO(),1)));
  }

  /**
   * Emit code for rule number 43:
   * r:	INT_USHR(INT_SHL(load8_16_32, INT_CONSTANT), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code43(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, Binary.getResult(P(p)), setSize(consumeMO(),1)));
  }

  /**
   * Emit code for rule number 44:
   * r:	INT_AND(load16_32, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code44(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, Binary.getResult(P(p)), setSize(consumeMO(),2)));
  }

  /**
   * Emit code for rule number 45:
   * r:	INT_USHR(INT_SHL(load16_32, INT_CONSTANT), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code45(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, Binary.getResult(P(p)), setSize(consumeMO(),2)));
  }

  /**
   * Emit code for rule number 46:
   * stm:	SHORT_STORE(riv, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code46(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 47:
   * stm:	SHORT_STORE(load16, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code47(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
EMIT(CPOS(PL(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), consumeMO()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 48:
   * stm:    SHORT_STORE(rlv, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code48(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 49:
   * stm:    SHORT_STORE(riv, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code49(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 50:
   * stm:	SHORT_ASTORE(riv, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code50(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 51:
   * stm:	SHORT_ASTORE(load16, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code51(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
EMIT(CPOS(PL(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), consumeMO()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 52:
   * stm:	SHORT_ASTORE(riv, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code52(AbstractBURS_TreeNode p) {
    RegisterOperand index = AStore.getIndex(P(p)).asRegister(); 
if (VM.BuildFor64Addr && index.getRegister().isInteger()) { 
  CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), AStore.getValue(P(p)))); 
} else { 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), AStore.getValue(P(p)))); 
}
  }

  /**
   * Emit code for rule number 53:
   * stm:	INT_ASTORE(riv, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code53(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 54:
   * stm:	INT_ASTORE(riv, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code54(AbstractBURS_TreeNode p) {
    RegisterOperand index=AStore.getIndex(P(p)).asRegister(); 
if (VM.BuildFor64Addr && index.getRegister().isInteger()) { 
  CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p)))); 
} else { 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p)))); 
}
  }

  /**
   * Emit code for rule number 55:
   * stm:	INT_ASTORE(riv, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code55(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 56:
   * stm:	INT_ASTORE(riv, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code56(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 57:
   * stm:	INT_ASTORE(riv, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code57(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 58:
   * stm:	LONG_ASTORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code58(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr){
  RegisterOperand hval = (RegisterOperand)AStore.getClearValue(P(p)); 
  hval.setType(TypeReference.Int); 
  RegisterOperand lval = new RegisterOperand(regpool.getSecondReg(hval.getRegister()), TypeReference.Int); 
  EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_AS(P(p), QW_S, DW, DW).copy(), hval))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, DW), lval));
} else {
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 59:
   * stm:	LONG_ASTORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code59(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) {
  RegisterOperand hval = (RegisterOperand)AStore.getClearValue(P(p)); 
  hval.setType(TypeReference.Int); 
  RegisterOperand lval = new RegisterOperand(regpool.getSecondReg(hval.getRegister()), TypeReference.Int); 
  EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_AS(P(p), QW_S, DW, DW).copy(), hval))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, DW), lval));
} else {
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 60:
   * stm:	LONG_ASTORE(r, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code60(AbstractBURS_TreeNode p) {
    RegisterOperand index=AStore.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()) { 
  CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
}
if (VM.BuildFor32Addr) {
  RegisterOperand hval = (RegisterOperand)AStore.getClearValue(P(p)); 
  hval.setType(TypeReference.Int); 
  RegisterOperand lval = new RegisterOperand(regpool.getSecondReg(hval.getRegister()), TypeReference.Int); 
  EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_AS(P(p), QW_S, DW, DW).copy(), hval))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, DW), lval));
} else {
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 61:
   * stm:	LONG_ASTORE(LONG_CONSTANT, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code61(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) {
  LongConstantOperand val = LC(AStore.getValue(P(p))); 
  EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_AS(P(p), QW_S, DW, DW).copy(), IC(val.upper32())))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, DW), IC(val.lower32())));
} else {
  LongConstantOperand val = LC(AStore.getValue(P(p))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, QW), LC(val)));
}
  }

  /**
   * Emit code for rule number 62:
   * stm:	LONG_ASTORE(LONG_CONSTANT, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code62(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) {
  LongConstantOperand val = LC(AStore.getValue(P(p))); 
  EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_AS(P(p), QW_S, DW, DW).copy(), IC(val.upper32())))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, DW), IC(val.lower32())));
} else {
  LongConstantOperand val = LC(AStore.getValue(P(p))); 
  EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), QW_S, QW), LC(val)));
}
  }

  /**
   * Emit code for rule number 63:
   * r:	LONG_CMP(rlv,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code63(AbstractBURS_TreeNode p) {
    LONG_CMP(P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 64:
   * stm:	GOTO
   * @param p BURS node to apply the rule to
   */
  private void code64(AbstractBURS_TreeNode p) {
    EMIT(MIR_Branch.mutate(P(p), IA32_JMP, Goto.getTarget(P(p))));
  }

  /**
   * Emit code for rule number 65:
   * stm:	PREFETCH(r)
   * @param p BURS node to apply the rule to
   */
  private void code65(AbstractBURS_TreeNode p) {
    EMIT(MIR_CacheOp.mutate(P(p), IA32_PREFETCHNTA, R(CacheOp.getRef(P(p)))));
  }

  /**
   * Emit code for rule number 66:
   * stm:	WRITE_FLOOR
   * @param p BURS node to apply the rule to
   */
  private void code66(AbstractBURS_TreeNode p) {
    EMIT(P(p)); // Pass through to maintain barrier semantics for code motion
  }

  /**
   * Emit code for rule number 67:
   * stm:	READ_CEILING
   * @param p BURS node to apply the rule to
   */
  private void code67(AbstractBURS_TreeNode p) {
    EMIT(P(p)); // Pass through to maintain barrier semantics for code motion
  }

  /**
   * Emit code for rule number 68:
   * stm:	FENCE
   * @param p BURS node to apply the rule to
   */
  private void code68(AbstractBURS_TreeNode p) {
    EMIT(MIR_Empty.mutate(P(p), IA32_MFENCE));
  }

  /**
   * Emit code for rule number 69:
   * stm:	PAUSE
   * @param p BURS node to apply the rule to
   */
  private void code69(AbstractBURS_TreeNode p) {
    EMIT(MIR_Empty.mutate(P(p), IA32_PAUSE));
  }

  /**
   * Emit code for rule number 70:
   * stm:	ILLEGAL_INSTRUCTION
   * @param p BURS node to apply the rule to
   */
  private void code70(AbstractBURS_TreeNode p) {
    EMIT(MIR_Empty.mutate(P(p), IA32_UD2));
  }

  /**
   * Emit code for rule number 71:
   * stm:	RETURN(NULL)
   * @param p BURS node to apply the rule to
   */
  private void code71(AbstractBURS_TreeNode p) {
    EMIT(MIR_Return.mutate(P(p), IA32_RET, null, null, null));
  }

  /**
   * Emit code for rule number 72:
   * stm:	RETURN(INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code72(AbstractBURS_TreeNode p) {
    EMIT(MIR_Return.mutate(P(p), IA32_RET, null, Return.getVal(P(p)), null));
  }

  /**
   * Emit code for rule number 73:
   * stm:	RETURN(r)
   * @param p BURS node to apply the rule to
   */
  private void code73(AbstractBURS_TreeNode p) {
    RegisterOperand ret = R(Return.getVal(P(p)));            
RegisterOperand ret2 = null;	                            
if (VM.BuildFor32Addr && ret.getType().isLongType()) {                                 
  ret.setType(TypeReference.Int);                           
  ret2 = new RegisterOperand(regpool.getSecondReg(ret.getRegister()), TypeReference.Int); 
}                                                            
EMIT(MIR_Return.mutate(P(p), IA32_RET, null, ret, ret2));
  }

  /**
   * Emit code for rule number 74:
   * stm:	RETURN(LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code74(AbstractBURS_TreeNode p) {
    LongConstantOperand val = LC(Return.getVal(P(p))); 
if (VM.BuildFor32Addr) {                           
  EMIT(MIR_Return.mutate(P(p), IA32_RET, null, IC(val.upper32()), IC(val.lower32()))); 
} else {                                           
  EMIT(MIR_Return.mutate(P(p), IA32_RET, null, val, null)); 
}
  }

  /**
   * Emit code for rule number 75:
   * r:	CALL(r, any)
   * @param p BURS node to apply the rule to
   */
  private void code75(AbstractBURS_TreeNode p) {
    CALL(P(p), Call.getAddress(P(p)));
  }

  /**
   * Emit code for rule number 76:
   * r:	CALL(BRANCH_TARGET, any)
   * @param p BURS node to apply the rule to
   */
  private void code76(AbstractBURS_TreeNode p) {
    CALL(P(p), Call.getAddress(P(p)));
  }

  /**
   * Emit code for rule number 77:
   * r:	CALL(INT_LOAD(riv, riv), any)
   * @param p BURS node to apply the rule to
   */
  private void code77(AbstractBURS_TreeNode p) {
    CALL(P(p), MO_L(PL(p), DW));
  }

  /**
   * Emit code for rule number 78:
   * r:	CALL(INT_CONSTANT, any)
   * @param p BURS node to apply the rule to
   */
  private void code78(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Int); 
EMIT(MIR_Move.create(IA32_MOV, temp, Call.getAddress(P(p)))); 
CALL(P(p), temp.copyRO());
  }

  /**
   * Emit code for rule number 79:
   * r:	CALL(LONG_LOAD(rlv, rlv), any)
   * @param p BURS node to apply the rule to
   */
  private void code79(AbstractBURS_TreeNode p) {
    CALL(P(p), MO_L(PL(p), QW));
  }

  /**
   * Emit code for rule number 80:
   * r:	SYSCALL(r, any)
   * @param p BURS node to apply the rule to
   */
  private void code80(AbstractBURS_TreeNode p) {
    SYSCALL(P(p), Call.getAddress(P(p)));
  }

  /**
   * Emit code for rule number 81:
   * r:	SYSCALL(INT_LOAD(riv, riv), any)
   * @param p BURS node to apply the rule to
   */
  private void code81(AbstractBURS_TreeNode p) {
    SYSCALL(P(p), MO_L(PL(p), DW));
  }

  /**
   * Emit code for rule number 82:
   * r:	SYSCALL(INT_CONSTANT, any)
   * @param p BURS node to apply the rule to
   */
  private void code82(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Int); 
EMIT(MIR_Move.create(IA32_MOV, temp, Call.getAddress(P(p)))); 
SYSCALL(P(p), temp.copyRO());
  }

  /**
   * Emit code for rule number 83:
   * r:      GET_TIME_BASE
   * @param p BURS node to apply the rule to
   */
  private void code83(AbstractBURS_TreeNode p) {
    GET_TIME_BASE(P(p), Nullary.getResult(P(p)));
  }

  /**
   * Emit code for rule number 84:
   * stm:	YIELDPOINT_OSR(any, any)
   * @param p BURS node to apply the rule to
   */
  private void code84(AbstractBURS_TreeNode p) {
    OSR(burs, P(p));
  }

  /**
   * Emit code for rule number 87:
   * address:	INT_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code87(AbstractBURS_TreeNode p) {
    pushAddress(R(Binary.getVal1(P(p))), R(Binary.getVal2(P(p))), B_S, Offset.zero());
  }

  /**
   * Emit code for rule number 88:
   * address:	INT_ADD(r, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code88(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal1(P(p)));
  }

  /**
   * Emit code for rule number 89:
   * address:	INT_ADD(address1scaledreg, r)
   * @param p BURS node to apply the rule to
   */
  private void code89(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 90:
   * address:	INT_ADD(address1scaledreg, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code90(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 91:
   * address:	INT_ADD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code91(AbstractBURS_TreeNode p) {
    combineAddresses();
  }

  /**
   * Emit code for rule number 92:
   * address:	INT_ADD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code92(AbstractBURS_TreeNode p) {
    combineAddresses();
  }

  /**
   * Emit code for rule number 93:
   * address1reg:	INT_ADD(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code93(AbstractBURS_TreeNode p) {
    pushAddress(R(Binary.getVal1(P(p))), null, B_S, Offset.fromIntSignExtend(VR(p)));
  }

  /**
   * Emit code for rule number 94:
   * address1reg:	INT_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code94(AbstractBURS_TreeNode p) {
    pushAddress(R(Move.getVal(P(p))), null, B_S, Offset.zero());
  }

  /**
   * Emit code for rule number 96:
   * address1reg:	INT_ADD(address1reg, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code96(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 99:
   * address1scaledreg:	INT_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code99(AbstractBURS_TreeNode p) {
    pushAddress(null, Binary.getVal1(P(p)).asRegister(), LEA_SHIFT(Binary.getVal2(P(p))), Offset.zero());
  }

  /**
   * Emit code for rule number 100:
   * address1scaledreg:	INT_ADD(address1scaledreg, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code100(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 101:
   * r:	ADDR_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code101(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)), false);
  }

  /**
   * Emit code for rule number 102:
   * r:	ADDR_2LONG(load32)
   * @param p BURS node to apply the rule to
   */
  private void code102(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), consumeMO(), false);
  }

  /**
   * Emit code for rule number 103:
   * r:	ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code103(AbstractBURS_TreeNode p) {
    ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 104:
   * r:	ATTEMPT_INT(riv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code104(AbstractBURS_TreeNode p) {
    ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 105:
   * r:	ATTEMPT_INT(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code105(AbstractBURS_TreeNode p) {
    ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 106:
   * r:	ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code106(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 107:
   * r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code107(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 108:
   * r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code108(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 109:
   * r:	ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code109(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 110:
   * r:	ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code110(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 111:
   * r:	ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code111(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 112:
   * stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code112(AbstractBURS_TreeNode p) {
    ATTEMPT_INT_IFCMP(MO(Attempt.getAddress(PL(p)), Attempt.getOffset(PL(p)), DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 113:
   * stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code113(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 114:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code114(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 115:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code115(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 116:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code116(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 117:
   * stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code117(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 118:
   * stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code118(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 119:
   * stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code119(AbstractBURS_TreeNode p) {
    ATTEMPT_INT_IFCMP(MO(Attempt.getAddress(PL(p)), Attempt.getOffset(PL(p)), DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 120:
   * stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code120(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 121:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code121(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 122:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code122(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 123:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code123(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 124:
   * stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code124(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 125:
   * stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code125(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 126:
   * r:	ATTEMPT_LONG(riv, OTHER_OPERAND(riv, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code126(AbstractBURS_TreeNode p) {
    ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getClearOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 127:
   * bittest:	INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code127(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), Binary.getVal1(PLR(p)).copy()));
  }

  /**
   * Emit code for rule number 128:
   * bittest:	INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code128(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VLRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PLR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VLRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 129:
   * bittest:	INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code129(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), IC(VLR(p))));
  }

  /**
   * Emit code for rule number 130:
   * bittest:	INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code130(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), Binary.getVal1(PLR(p)).copy()));
  }

  /**
   * Emit code for rule number 131:
   * bittest:	INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code131(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VLRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PLR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VLRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 132:
   * bittest:	INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code132(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), IC(VLR(p))));
  }

  /**
   * Emit code for rule number 133:
   * bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
   * @param p BURS node to apply the rule to
   */
  private void code133(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal2(P(p)), Binary.getVal1(PLR(p)).copy()));
  }

  /**
   * Emit code for rule number 134:
   * bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)),load32)
   * @param p BURS node to apply the rule to
   */
  private void code134(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VLRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PLR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VLRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 135:
   * bittest:	INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code135(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(P(p)), Binary.getVal1(PRR(p)).copy()));
  }

  /**
   * Emit code for rule number 136:
   * bittest:	INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code136(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VRRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PRR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VRRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 137:
   * r:	BOOLEAN_CMP_INT(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code137(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), 
   BooleanCmp.getClearVal1(P(p)), BooleanCmp.getClearVal2(P(p)), 
   BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 138:
   * boolcmp: BOOLEAN_CMP_INT(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code138(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, BooleanCmp.getClearVal1(P(p)), BooleanCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 139:
   * r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code139(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p),MIR_Test.create(IA32_TEST, BooleanCmp.getVal1(P(p)).copy(), BooleanCmp.getClearVal1(P(p)))));
BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 140:
   * boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code140(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p))); 
EMIT(CPOS(P(p),MIR_Test.create(IA32_TEST, BooleanCmp.getVal1(P(p)).copy(), BooleanCmp.getClearVal1(P(p)))));
  }

  /**
   * Emit code for rule number 141:
   * r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code141(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SHR, P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getClearVal1(P(p)), IC(31));
  }

  /**
   * Emit code for rule number 142:
   * r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code142(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SHR, P(p), BooleanCmp.getResult(P(p)), consumeMO(), IC(31));
  }

  /**
   * Emit code for rule number 143:
   * r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code143(AbstractBURS_TreeNode p) {
    RegisterOperand result = BooleanCmp.getResult(P(p)); 
EMIT_Commutative(IA32_SHR, P(p), result, BooleanCmp.getClearVal1(P(p)), IC(31)); 
EMIT(CPOS(P(p),MIR_BinaryAcc.create(IA32_XOR, result.copyRO(), IC(1))));
  }

  /**
   * Emit code for rule number 144:
   * r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code144(AbstractBURS_TreeNode p) {
    RegisterOperand result = BooleanCmp.getResult(P(p)); 
EMIT_Commutative(IA32_SHR, P(p), result, consumeMO(), IC(31)); 
EMIT(CPOS(P(p),MIR_BinaryAcc.create(IA32_XOR, result.copyRO(), IC(1))));
  }

  /**
   * Emit code for rule number 145:
   * r:	BOOLEAN_CMP_INT(cz, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code145(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 146:
   * boolcmp: BOOLEAN_CMP_INT(cz, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code146(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 147:
   * r:	BOOLEAN_CMP_INT(szp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code147(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 148:
   * boolcmp: BOOLEAN_CMP_INT(szp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code148(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 149:
   * r:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code149(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BIT_TEST(VR(p),BooleanCmp.getCond(P(p))));
  }

  /**
   * Emit code for rule number 150:
   * boolcmp:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code150(AbstractBURS_TreeNode p) {
    pushCOND(BIT_TEST(VR(p),BooleanCmp.getCond(P(p))));
  }

  /**
   * Emit code for rule number 151:
   * r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code151(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), consumeCOND());
  }

  /**
   * Emit code for rule number 153:
   * r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code153(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), consumeCOND().flipCode());
  }

  /**
   * Emit code for rule number 154:
   * boolcmp:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code154(AbstractBURS_TreeNode p) {
    pushCOND(consumeCOND().flipCode()); // invert already pushed condition
  }

  /**
   * Emit code for rule number 155:
   * r:	BOOLEAN_CMP_INT(load32,riv)
   * @param p BURS node to apply the rule to
   */
  private void code155(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(PL(p), BooleanCmp.getClearResult(P(p)), 
            consumeMO(), BooleanCmp.getClearVal2(P(p)), 
	    BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 156:
   * boolcmp: BOOLEAN_CMP_INT(load32,riv)
   * @param p BURS node to apply the rule to
   */
  private void code156(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, consumeMO(), BooleanCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 157:
   * r:	BOOLEAN_CMP_INT(r,load32)
   * @param p BURS node to apply the rule to
   */
  private void code157(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(PR(p), BooleanCmp.getClearResult(P(p)), 
            BooleanCmp.getClearVal1(P(p)), consumeMO(), 
	    BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 158:
   * boolcmp: BOOLEAN_CMP_INT(riv,load32)
   * @param p BURS node to apply the rule to
   */
  private void code158(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, BooleanCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 159:
   * stm:	BYTE_STORE(boolcmp, OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code159(AbstractBURS_TreeNode p) {
    EMIT(MIR_Set.mutate(P(p), IA32_SET__B, MO_S(P(p),B), COND(consumeCOND())));
  }

  /**
   * Emit code for rule number 160:
   * stm:	BYTE_ASTORE(boolcmp, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code160(AbstractBURS_TreeNode p) {
    EMIT(MIR_Set.mutate(P(p), IA32_SET__B, MO_AS(P(p),B_S,B), COND(consumeCOND())));
  }

  /**
   * Emit code for rule number 161:
   * r:	BOOLEAN_CMP_LONG(rlv,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code161(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_LONG(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getVal1(P(p)), BooleanCmp.getVal2(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 162:
   * boolcmp: BOOLEAN_CMP_LONG(rlv,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code162(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p))); 
LONG_CMP(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getVal1(P(p)), BooleanCmp.getVal2(P(p))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, BooleanCmp.getResult(P(p)), IC(0))));
  }

  /**
   * Emit code for rule number 163:
   * r:	BOOLEAN_NOT(r)
   * @param p BURS node to apply the rule to
   */
  private void code163(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)), IC(1));
  }

  /**
   * Emit code for rule number 164:
   * stm:	BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code164(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), B), MO_S(P(p), B), IC(1));
  }

  /**
   * Emit code for rule number 165:
   * stm:	BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code165(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), B_S, B), MO_AS(P(p), B_S, B), IC(1));
  }

  /**
   * Emit code for rule number 166:
   * stm:    BYTE_STORE(riv, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code166(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), B), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 167:
   * stm:    BYTE_STORE(load8, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code167(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
EMIT(CPOS(PL(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), consumeMO()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), B), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 168:
   * stm:    BYTE_ASTORE(riv, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code168(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), B_S, B), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 169:
   * stm:    BYTE_ASTORE(load8, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code169(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
EMIT(CPOS(PL(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), consumeMO()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), B_S, B), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 170:
   * r: CMP_CMOV(r, OTHER_OPERAND(riv, any))
   * @param p BURS node to apply the rule to
   */
  private void code170(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP,  CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 171:
   * r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code171(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Test.create(IA32_TEST, CondMove.getVal1(P(p)).copy(), CondMove.getClearVal1(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 172:
   * r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code172(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SAR, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), IC(31));
  }

  /**
   * Emit code for rule number 173:
   * r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code173(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SAR, P(p), CondMove.getClearResult(P(p)), consumeMO(), IC(31));
  }

  /**
   * Emit code for rule number 174:
   * r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code174(AbstractBURS_TreeNode p) {
    RegisterOperand result = CondMove.getClearResult(P(p)); 
EMIT_Commutative(IA32_SAR, P(p), result, CondMove.getClearVal1(P(p)), IC(31)); 
EMIT(CPOS(P(p),MIR_UnaryAcc.create(IA32_NOT, result.copyRO())));
  }

  /**
   * Emit code for rule number 175:
   * r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code175(AbstractBURS_TreeNode p) {
    RegisterOperand result = CondMove.getClearResult(P(p)); 
EMIT_Commutative(IA32_SAR, P(p), result, consumeMO(), IC(31)); 
EMIT(CPOS(P(p),MIR_UnaryAcc.create(IA32_NOT, result.copyRO())));
  }

  /**
   * Emit code for rule number 176:
   * r: CMP_CMOV(load8, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code176(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 177:
   * r: CMP_CMOV(uload8, OTHER_OPERAND(riv, any))
   * @param p BURS node to apply the rule to
   */
  private void code177(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 178:
   * r: CMP_CMOV(riv, OTHER_OPERAND(uload8, any))
   * @param p BURS node to apply the rule to
   */
  private void code178(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 179:
   * r: CMP_CMOV(sload16, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code179(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 180:
   * r: CMP_CMOV(load32, OTHER_OPERAND(riv, any))
   * @param p BURS node to apply the rule to
   */
  private void code180(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 181:
   * r: CMP_CMOV(riv, OTHER_OPERAND(load32, any))
   * @param p BURS node to apply the rule to
   */
  private void code181(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal1(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).flipOperands(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 182:
   * r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code182(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), consumeCOND(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 183:
   * r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code183(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), consumeCOND().flipCode(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 184:
   * r: CMP_CMOV(bittest, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code184(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), BIT_TEST(VRL(p), CondMove.getClearCond(P(p))), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 185:
   * r: CMP_CMOV(cz, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code185(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 186:
   * r: CMP_CMOV(szp, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code186(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 187:
   * r:	INT_2BYTE(r)
   * @param p BURS node to apply the rule to
   */
  private void code187(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Unary.getResult(P(p)), Unary.getVal(P(p))));
  }

  /**
   * Emit code for rule number 188:
   * r:	INT_2BYTE(load8_16_32)
   * @param p BURS node to apply the rule to
   */
  private void code188(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Unary.getResult(P(p)), consumeMO()));
  }

  /**
   * Emit code for rule number 189:
   * stm:	BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code189(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), B), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 190:
   * stm:	BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code190(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), B_S, B), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 191:
   * r:	INT_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code191(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)), true);
  }

  /**
   * Emit code for rule number 192:
   * r:	INT_2LONG(load32)
   * @param p BURS node to apply the rule to
   */
  private void code192(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 193:
   * r:      LONG_AND(INT_2LONG(r), LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code193(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Binary.getClearResult(P(p)), Unary.getClearVal(PL(p)), false);
  }

  /**
   * Emit code for rule number 194:
   * r:      LONG_AND(INT_2LONG(load32), LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code194(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Binary.getClearResult(P(p)), consumeMO(), false);
  }

  /**
   * Emit code for rule number 195:
   * r:      LONG_SHL(INT_2LONG(r), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code195(AbstractBURS_TreeNode p) {
    Register hr = Binary.getClearResult(P(p)).getRegister(); 
Register lr = regpool.getSecondReg(hr); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, new RegisterOperand(hr, TypeReference.Int), Unary.getClearVal(PL(p)))); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(lr, TypeReference.Int), IC(0))));
  }

  /**
   * Emit code for rule number 196:
   * r:      LONG_SHL(INT_2LONG(load64), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code196(AbstractBURS_TreeNode p) {
    Register hr = Binary.getClearResult(P(p)).getRegister(); 
Register lr = regpool.getSecondReg(hr); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, new RegisterOperand(hr, TypeReference.Int), setSize(consumeMO(),4))); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(lr, TypeReference.Int), IC(0))));
  }

  /**
   * Emit code for rule number 197:
   * r:	INT_2SHORT(r)
   * @param p BURS node to apply the rule to
   */
  private void code197(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, Unary.getResult(P(p)), Unary.getVal(P(p)))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSXQ__W, Unary.getResult(P(p)), Unary.getVal(P(p)))); 
}
  }

  /**
   * Emit code for rule number 198:
   * r:	INT_2SHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code198(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, Unary.getResult(P(p)), setSize(consumeMO(), 2))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSXQ__W, Unary.getResult(P(p)), setSize(consumeMO(), 2))); 
}
  }

  /**
   * Emit code for rule number 199:
   * sload16:	INT_2SHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code199(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(),2));
  }

  /**
   * Emit code for rule number 200:
   * stm:	SHORT_STORE(INT_2SHORT(r), OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code200(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 201:
   * stm:	SHORT_ASTORE(INT_2SHORT(r), OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code201(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 202:
   * szpr:	INT_2USHORT(r)
   * @param p BURS node to apply the rule to
   */
  private void code202(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, Unary.getResult(P(p)).copyRO(), Unary.getClearVal(P(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_AND, Unary.getResult(P(p)), IC(0xFFFF)));
  }

  /**
   * Emit code for rule number 203:
   * uload16:	INT_2USHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code203(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(),2));
  }

  /**
   * Emit code for rule number 204:
   * r:	INT_2USHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code204(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, Unary.getResult(P(p)), setSize(consumeMO(),2)));
  }

  /**
   * Emit code for rule number 205:
   * stm:	SHORT_STORE(INT_2USHORT(r), OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code205(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 206:
   * stm:	SHORT_ASTORE(INT_2USHORT(r), OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code206(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 207:
   * czr:	INT_ADD(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code207(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 208:
   * r:	INT_ADD(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code208(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isIntConstant()) { 
 pushAddress(R(Binary.getClearVal1(P(p))), null, B_S, Offset.fromIntSignExtend(VR(p))); 
} else { 
 pushAddress(R(Binary.getClearVal1(P(p))), R(Binary.getClearVal2(P(p))), B_S, Offset.zero()); 
} 
EMIT_Lea(P(p), Binary.getClearResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 209:
   * czr:	INT_ADD(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code209(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 210:
   * czr:	INT_ADD(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code210(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 211:
   * stm:	INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code211(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 212:
   * stm:	INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code212(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 213:
   * stm:	INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code213(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 214:
   * stm:	INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code214(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 215:
   * szpr:	INT_AND(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code215(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 216:
   * szp:	INT_AND(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code216(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))));
  }

  /**
   * Emit code for rule number 217:
   * szpr:	INT_AND(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code217(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 218:
   * szpr:	INT_AND(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code218(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 219:
   * szp:	INT_AND(load8_16_32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code219(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, consumeMO(), Binary.getClearVal2(P(p))));
  }

  /**
   * Emit code for rule number 220:
   * szp:	INT_AND(r, load8_16_32)
   * @param p BURS node to apply the rule to
   */
  private void code220(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, consumeMO(), Binary.getClearVal1(P(p))));
  }

  /**
   * Emit code for rule number 221:
   * stm:	INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code221(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 222:
   * stm:	INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code222(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 223:
   * stm:	INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code223(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 224:
   * stm:	INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code224(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 225:
   * r:	INT_DIV(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code225(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), true, true);
  }

  /**
   * Emit code for rule number 226:
   * r:	INT_DIV(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code226(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            consumeMO(), true, true);
  }

  /**
   * Emit code for rule number 227:
   * r:     UNSIGNED_DIV_64_32(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code227(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            GuardedBinary.getVal2(P(p)), true, false);
  }

  /**
   * Emit code for rule number 228:
   * r:     UNSIGNED_DIV_64_32(rlv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code228(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            consumeMO(), true, false);
  }

  /**
   * Emit code for rule number 229:
   * stm:	INT_IFCMP(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code229(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 230:
   * stm:	INT_IFCMP(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code230(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Test.create(IA32_TEST, IfCmp.getVal1(P(p)).copy(), IfCmp.getClearVal1(P(p))))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 231:
   * stm:	INT_IFCMP(load8, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code231(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 232:
   * stm:	INT_IFCMP(uload8, r)
   * @param p BURS node to apply the rule to
   */
  private void code232(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 233:
   * stm:	INT_IFCMP(r, uload8)
   * @param p BURS node to apply the rule to
   */
  private void code233(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), consumeMO(), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 234:
   * stm:	INT_IFCMP(sload16, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code234(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 235:
   * stm:	INT_IFCMP(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code235(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 236:
   * stm:	INT_IFCMP(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code236(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), consumeMO(), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 237:
   * stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code237(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(consumeCOND()), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 238:
   * stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code238(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(consumeCOND().flipCode()), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 239:
   * stm:	INT_IFCMP(cz, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code239(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 240:
   * stm:	INT_IFCMP(szp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code240(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 241:
   * stm:	INT_IFCMP(bittest, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code241(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(BIT_TEST(VR(p), IfCmp.getCond(P(p)))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 242:
   * stm:	INT_IFCMP2(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code242(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp2.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, IfCmp2.getClearVal1(P(p)), IfCmp2.getClearVal2(P(p))))); 
EMIT(MIR_CondBranch2.mutate(P(p), IA32_JCC2,                                  
	                    COND(IfCmp2.getCond1(P(p))), IfCmp2.getClearTarget1(P(p)),IfCmp2.getClearBranchProfile1(P(p)), 
	                    COND(IfCmp2.getCond2(P(p))), IfCmp2.getClearTarget2(P(p)), IfCmp2.getClearBranchProfile2(P(p))));
  }

  /**
   * Emit code for rule number 243:
   * stm:	INT_IFCMP2(load32,riv)
   * @param p BURS node to apply the rule to
   */
  private void code243(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp2.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), IfCmp2.getClearVal2(P(p))))); 
EMIT(MIR_CondBranch2.mutate(P(p), IA32_JCC2,                                  
	                    COND(IfCmp2.getCond1(P(p))), IfCmp2.getClearTarget1(P(p)),IfCmp2.getClearBranchProfile1(P(p)), 
	                    COND(IfCmp2.getCond2(P(p))), IfCmp2.getClearTarget2(P(p)), IfCmp2.getClearBranchProfile2(P(p))));
  }

  /**
   * Emit code for rule number 244:
   * stm:	INT_IFCMP2(riv,load32)
   * @param p BURS node to apply the rule to
   */
  private void code244(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp2.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), IfCmp2.getClearVal1(P(p))))); 
EMIT(MIR_CondBranch2.mutate(P(p), IA32_JCC2,                                  
	                    COND(IfCmp2.getCond1(P(p)).flipOperands()), IfCmp2.getClearTarget1(P(p)),IfCmp2.getClearBranchProfile1(P(p)), 
	                    COND(IfCmp2.getCond2(P(p)).flipOperands()), IfCmp2.getClearTarget2(P(p)), IfCmp2.getClearBranchProfile2(P(p))));
  }

  /**
   * Emit code for rule number 245:
   * r:	INT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code245(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 246:
   * r:	INT_LOAD(riv, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code246(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getAddress(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
		     consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 247:
   * r:	INT_LOAD(address1scaledreg, riv)
   * @param p BURS node to apply the rule to
   */
  private void code247(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 248:
   * r:	INT_LOAD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code248(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 249:
   * r:	INT_LOAD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code249(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 250:
   * r:	INT_LOAD(address, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code250(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 251:
   * r:      INT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code251(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 252:
   * r:	INT_MOVE(riv)
   * @param p BURS node to apply the rule to
   */
  private void code252(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 253:
   * czr:	INT_MOVE(czr)
   * @param p BURS node to apply the rule to
   */
  private void code253(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 255:
   * szpr:	INT_MOVE(szpr)
   * @param p BURS node to apply the rule to
   */
  private void code255(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 264:
   * r:	INT_MUL(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code264(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 265:
   * r:	INT_MUL(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code265(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 266:
   * r:	INT_MUL(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code266(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 267:
   * szpr:	INT_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code267(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 268:
   * stm:	INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code268(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), MO_S(P(p), DW), MO_S(P(p), DW));
  }

  /**
   * Emit code for rule number 269:
   * stm:	INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code269(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 270:
   * r:	INT_NOT(r)
   * @param p BURS node to apply the rule to
   */
  private void code270(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 271:
   * stm:	INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code271(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), MO_S(P(p), DW), MO_S(P(p), DW));
  }

  /**
   * Emit code for rule number 272:
   * stm:	INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code272(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 273:
   * szpr:	INT_OR(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code273(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 274:
   * szpr:	INT_OR(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code274(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 275:
   * szpr:	INT_OR(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code275(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 276:
   * stm:	INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code276(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 277:
   * stm:	INT_STORE(INT_OR(r, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code277(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 278:
   * stm:	INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code278(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 279:
   * stm:	INT_ASTORE(INT_OR(r, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code279(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 280:
   * r:	INT_REM(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code280(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
	    GuardedBinary.getClearVal2(P(p)), false, true);
  }

  /**
   * Emit code for rule number 281:
   * r:	INT_REM(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code281(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            consumeMO(), false, true);
  }

  /**
   * Emit code for rule number 282:
   * r:     UNSIGNED_REM_64_32(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code282(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            GuardedBinary.getVal2(P(p)), false, false);
  }

  /**
   * Emit code for rule number 283:
   * r:     UNSIGNED_REM_64_32(rlv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code283(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            consumeMO(), false, false);
  }

  /**
   * Emit code for rule number 284:
   * r:	INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code284(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(VLR(p)&0x1f));
  }

  /**
   * Emit code for rule number 285:
   * r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code285(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(VRR(p)&0x1f));
  }

  /**
   * Emit code for rule number 286:
   * r:      INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code286(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(1));
  }

  /**
   * Emit code for rule number 287:
   * r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code287(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(1));
  }

  /**
   * Emit code for rule number 288:
   * r:      INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code288(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 289:
   * r:      INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code289(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PRR(p))))); 
EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 290:
   * r:      INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code290(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PRR(p))))); 
EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 291:
   * r:      INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code291(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 292:
   * szpr:	INT_SHL(riv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code292(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 293:
   * szpr:	INT_SHL(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code293(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 294:
   * szpr:	INT_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code294(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 31); if(Binary.getVal2(P(p)).asIntConstant().value == 1) { 
 EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getVal1(P(p)).copy(), Binary.getClearVal1(P(p))); 
} else { 
 EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 295:
   * r:	INT_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code295(AbstractBURS_TreeNode p) {
    pushAddress(null, Binary.getClearVal1(P(p)).asRegister(), LEA_SHIFT(Binary.getClearVal2(P(p))), Offset.zero()); 
EMIT_Lea(P(p), Binary.getClearResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 296:
   * szpr:	INT_SHL(INT_SHR(r, INT_CONSTANT), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code296(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(0xffffffff << VR(p)));
  }

  /**
   * Emit code for rule number 297:
   * stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code297(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_S(P(p), DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 298:
   * stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code298(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 31); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 299:
   * stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code299(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_AS(P(p), DW_S, DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 300:
   * stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code300(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 301:
   * szpr:	INT_SHR(riv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code301(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 302:
   * szpr:	INT_SHR(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code302(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 303:
   * szpr:	INT_SHR(riv, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code303(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 31); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 304:
   * stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code304(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_S(P(p), DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 305:
   * stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code305(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 31); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 306:
   * stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code306(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_AS(P(p), DW_S, DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 307:
   * stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code307(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 308:
   * stm:	INT_STORE(riv, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code308(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 309:
   * stm:	INT_STORE(riv, OTHER_OPERAND(riv, address1scaledreg))
   * @param p BURS node to apply the rule to
   */
  private void code309(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getAddress(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, 
                     consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 310:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, riv))
   * @param p BURS node to apply the rule to
   */
  private void code310(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, 
                     consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 311:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, address1reg))
   * @param p BURS node to apply the rule to
   */
  private void code311(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
                    consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
                    Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 312:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address1reg, address1scaledreg))
   * @param p BURS node to apply the rule to
   */
  private void code312(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
                    consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
                    Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 313:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code313(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
	             consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 314:
   * czr:	INT_SUB(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code314(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 315:
   * r:	INT_SUB(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code315(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, Binary.getResult(P(p)).copy()))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, Binary.getResult(P(p)), Binary.getVal1(P(p))));
  }

  /**
   * Emit code for rule number 316:
   * r:	INT_SUB(load32, r)
   * @param p BURS node to apply the rule to
   */
  private void code316(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, Binary.getResult(P(p)).copy()))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, Binary.getResult(P(p)), consumeMO()));
  }

  /**
   * Emit code for rule number 317:
   * czr:	INT_SUB(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code317(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 318:
   * czr:	INT_SUB(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code318(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getResult(P(p)), consumeMO(), Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 319:
   * stm:	INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code319(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SUB, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 320:
   * stm:	INT_STORE(INT_SUB(riv, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code320(AbstractBURS_TreeNode p) {
    MemoryOperand result = MO_S(P(p), DW); 
EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, result))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, result.copy(), Binary.getClearVal1(PL(p))));
  }

  /**
   * Emit code for rule number 321:
   * stm:	INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code321(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SUB, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 322:
   * stm:	INT_ASTORE(INT_SUB(riv, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code322(AbstractBURS_TreeNode p) {
    MemoryOperand result = MO_AS(P(p), DW_S, DW); 
EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, result))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, result.copy(), Binary.getClearVal1(PL(p))));
  }

  /**
   * Emit code for rule number 323:
   * szpr:	INT_USHR(riv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code323(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 324:
   * szpr:	INT_USHR(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code324(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 325:
   * szpr:	INT_USHR(riv, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code325(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 31); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 326:
   * stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code326(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_S(P(p), DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 327:
   * stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code327(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 31); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 328:
   * stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code328(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_AS(P(p), DW_S, DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 329:
   * stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code329(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 330:
   * szpr:	INT_XOR(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code330(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 331:
   * szpr:	INT_XOR(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code331(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 332:
   * szpr:	INT_XOR(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code332(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 333:
   * stm:	INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code333(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 334:
   * stm:	INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code334(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 335:
   * stm:	INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code335(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 336:
   * stm:	INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code336(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 337:
   * r: LCMP_CMOV(r, OTHER_OPERAND(rlv, any))
   * @param p BURS node to apply the rule to
   */
  private void code337(AbstractBURS_TreeNode p) {
    LCMP_CMOV(P(p), CondMove.getResult(P(p)), CondMove.getVal1(P(p)), CondMove.getVal2(P(p)),
          CondMove.getCond(P(p)), CondMove.getTrueValue(P(p)), CondMove.getFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 338:
   * r:	INT_ADD(address1scaledreg, r)
   * @param p BURS node to apply the rule to
   */
  private void code338(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p))); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 339:
   * r:	INT_ADD(r, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code339(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal1(P(p))); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 340:
   * r:	INT_ADD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code340(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 341:
   * r:	INT_ADD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code341(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 342:
   * r:	INT_ADD(address, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code342(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p))); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 343:
   * r:	INT_MOVE(address)
   * @param p BURS node to apply the rule to
   */
  private void code343(AbstractBURS_TreeNode p) {
    EMIT_Lea(P(p), Move.getResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 344:
   * r:      BYTE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code344(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Load.getResult(P(p)), MO_L(P(p), B)));
  }

  /**
   * Emit code for rule number 345:
   * sload8:	BYTE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code345(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), B));
  }

  /**
   * Emit code for rule number 346:
   * r:      BYTE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code346(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B)));
  }

  /**
   * Emit code for rule number 347:
   * sload8:	BYTE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code347(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), B_S, B));
  }

  /**
   * Emit code for rule number 348:
   * r:      UBYTE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code348(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, Load.getResult(P(p)), MO_L(P(p), B)));
  }

  /**
   * Emit code for rule number 349:
   * uload8:	UBYTE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code349(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), B));
  }

  /**
   * Emit code for rule number 350:
   * r:      UBYTE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code350(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B)));
  }

  /**
   * Emit code for rule number 351:
   * uload8:	UBYTE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code351(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), B_S, B));
  }

  /**
   * Emit code for rule number 354:
   * r:      SHORT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code354(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, Load.getResult(P(p)), MO_L(P(p), W)));
  }

  /**
   * Emit code for rule number 355:
   * sload16: SHORT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code355(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), W));
  }

  /**
   * Emit code for rule number 356:
   * r:      SHORT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code356(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W)));
  }

  /**
   * Emit code for rule number 357:
   * sload16: SHORT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code357(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), W_S, W));
  }

  /**
   * Emit code for rule number 358:
   * r:      USHORT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code358(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, Load.getResult(P(p)), MO_L(P(p), W)));
  }

  /**
   * Emit code for rule number 359:
   * uload16: USHORT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code359(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), W));
  }

  /**
   * Emit code for rule number 360:
   * r:      USHORT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code360(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W)));
  }

  /**
   * Emit code for rule number 361:
   * uload16: USHORT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code361(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), W_S, W));
  }

  /**
   * Emit code for rule number 364:
   * load32:	INT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code364(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), DW));
  }

  /**
   * Emit code for rule number 365:
   * load32:	INT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code365(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 370:
   * load64:	LONG_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code370(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), QW));
  }

  /**
   * Emit code for rule number 371:
   * load64:	LONG_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code371(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 372:
   * r:	LONG_2INT(r)
   * @param p BURS node to apply the rule to
   */
  private void code372(AbstractBURS_TreeNode p) {
    RegisterOperand val = R(Unary.getVal(P(p)).copy()); 
if (VM.BuildFor64Addr) { 
RegisterOperand r = Unary.getResult(P(p)); 
RegisterOperand temp = regpool.makeTempInt(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, temp, val))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, r, temp.copy())); 
} else { 
Register lh = regpool.getSecondReg(R(Unary.getVal(P(p))).getRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), new RegisterOperand(lh, TypeReference.Int))); 
}
  }

  /**
   * Emit code for rule number 373:
   * stm:	INT_STORE(LONG_2INT(r), OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code373(AbstractBURS_TreeNode p) {
    RegisterOperand val = R(Unary.getVal(PL(p)).copy()); 
if (VM.BuildFor64Addr) { 
RegisterOperand temp = regpool.makeTempInt(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, temp, val))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), DW),temp.copy())); 
} else { 
Register lh = regpool.getSecondReg(R(Unary.getVal(PL(p))).getRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), DW), new RegisterOperand(lh, TypeReference.Int))); 
}
  }

  /**
   * Emit code for rule number 374:
   * stm:	INT_ASTORE(LONG_2INT(r), OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code374(AbstractBURS_TreeNode p) {
    RegisterOperand val = R(Unary.getVal(PL(p)).copy()); 
if (VM.BuildFor64Addr) { 
RegisterOperand temp = regpool.makeTempInt(); 
EMIT(CPOS(P(p),MIR_Move.create(IA32_MOV, temp, val))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW),temp.copy())); 
} else { 
Register lh = regpool.getSecondReg(R(Unary.getVal(PL(p))).getRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), DW_S, DW), new RegisterOperand(lh, TypeReference.Int))); 
}
  }

  /**
   * Emit code for rule number 375:
   * r:	LONG_2INT(load64)
   * @param p BURS node to apply the rule to
   */
  private void code375(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), setSize(consumeMO(), 4)));
  }

  /**
   * Emit code for rule number 376:
   * load32:      LONG_2INT(load64)
   * @param p BURS node to apply the rule to
   */
  private void code376(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(), 4));
  }

  /**
   * Emit code for rule number 377:
   * r:	LONG_2INT(LONG_USHR(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code377(AbstractBURS_TreeNode p) {
    RegisterOperand val = R(Binary.getVal1(PL(p))); 
if (VM.BuildFor64Addr) { 
RegisterOperand temp = regpool.makeTempInt(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, temp, val.copy()))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_SHR,temp.copy(),LC(32)))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), temp.copy())); 
} else { 
Register uh = Binary.getVal1(PL(p)).asRegister().getRegister(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), new RegisterOperand(uh, TypeReference.Int))); 
}
  }

  /**
   * Emit code for rule number 378:
   * r:      LONG_2INT(LONG_SHR(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code378(AbstractBURS_TreeNode p) {
    RegisterOperand val = R(Binary.getVal1(PL(p))); 
if (VM.BuildFor64Addr) { 
RegisterOperand temp = regpool.makeTempInt(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, temp, val.copy()))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_SAR,temp.copy(),LC(32)))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), temp.copy())); 
} else { 
Register uh = Binary.getVal1(PL(p)).asRegister().getRegister(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), new RegisterOperand(uh, TypeReference.Int))); 
}
  }

  /**
   * Emit code for rule number 379:
   * r:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code379(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), mo));
  }

  /**
   * Emit code for rule number 380:
   * r:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code380(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), mo));
  }

  /**
   * Emit code for rule number 381:
   * load32:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code381(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
pushMO(mo);
  }

  /**
   * Emit code for rule number 382:
   * load32:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code382(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
pushMO(mo);
  }

  /**
   * Emit code for rule number 383:
   * r:	LONG_ADD(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code383(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)), true);
  }

  /**
   * Emit code for rule number 384:
   * r:	LONG_ADD(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code384(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 385:
   * r:	LONG_ADD(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code385(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 386:
   * stm:	LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code386(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 387:
   * stm:	LONG_STORE(LONG_ADD(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code387(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 388:
   * stm:	LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code388(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 389:
   * stm:	LONG_ASTORE(LONG_ADD(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code389(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_ADD, IA32_ADC, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 390:
   * r:	LONG_AND(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code390(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), Binary.getVal2(P(p)), true);
  }

  /**
   * Emit code for rule number 391:
   * r:	LONG_AND(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code391(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 392:
   * r:	LONG_AND(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code392(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), Binary.getResult(P(p)), Binary.getVal2(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 393:
   * stm:	LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code393(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 394:
   * stm:	LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code394(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 395:
   * stm:	LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code395(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 396:
   * stm:	LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code396(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_AND, IA32_AND, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 397:
   * stm:	LONG_IFCMP(r,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code397(AbstractBURS_TreeNode p) {
    EMIT(P(p)); //  Leave for ComplexLIR2MIRExpansion
  }

  /**
   * Emit code for rule number 398:
   * r:	LONG_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code398(AbstractBURS_TreeNode p) {
    RegisterOperand hres = Load.getClearResult(P(p)); 
RegisterOperand lres = new RegisterOperand(regpool.getSecondReg(hres.getRegister()), TypeReference.Int); 
hres.setType(TypeReference.Int); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, hres, MO_L(P(p), DW, DW).copy()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, lres, MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 399:
   * r:      LONG_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code399(AbstractBURS_TreeNode p) {
    RegisterOperand hres = ALoad.getClearResult(P(p)); 
RegisterOperand lres = new RegisterOperand(regpool.getSecondReg(hres.getRegister()), TypeReference.Int); 
hres.setType(TypeReference.Int); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, hres, MO_AL(P(p), QW_S, DW, DW).copy()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, lres, MO_AL(P(p), QW_S, DW)));
  }

  /**
   * Emit code for rule number 400:
   * r:	LONG_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code400(AbstractBURS_TreeNode p) {
    Register res1 = Move.getResult(P(p)).getRegister();           
Register res2 = regpool.getSecondReg(res1);              
Register val1 = Move.getVal(P(p)).asRegister().getRegister(); 
Register val2 = regpool.getSecondReg(val1);              
EMIT(MIR_Move.mutate(P(p), IA32_MOV, new RegisterOperand(res1, TypeReference.Int), 
                     new RegisterOperand(val1, TypeReference.Int)));               
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(res2, TypeReference.Int), 
                     new RegisterOperand(val2, TypeReference.Int))));
  }

  /**
   * Emit code for rule number 401:
   * r:	LONG_MOVE(LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code401(AbstractBURS_TreeNode p) {
    Register res1 = Move.getResult(P(p)).getRegister();   
Register res2 = regpool.getSecondReg(res1);      
LongConstantOperand val = LC(Move.getVal(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, new RegisterOperand(res1, TypeReference.Int), IC(val.upper32()))); 
EMIT(CPOS(P(p),MIR_Move.create(IA32_MOV, new RegisterOperand(res2, TypeReference.Int), IC(val.lower32()))));
  }

  /**
   * Emit code for rule number 403:
   * r:	LONG_MUL(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code403(AbstractBURS_TreeNode p) {
    LONG_MUL(P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 404:
   * r:      LONG_MUL(LONG_AND(rlv, LONG_CONSTANT), LONG_AND(rlv, LONG_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code404(AbstractBURS_TreeNode p) {
    INT_TO_LONG_MUL(P(p), Binary.getResult(P(p)), Binary.getVal1(PL(p)), Binary.getVal1(PR(p)), false);
  }

  /**
   * Emit code for rule number 405:
   * r:      LONG_MUL(LONG_AND(rlv, LONG_CONSTANT), LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code405(AbstractBURS_TreeNode p) {
    INT_TO_LONG_MUL(P(p), Binary.getResult(P(p)), Binary.getVal1(PL(p)), Binary.getVal2(P(p)), false);
  }

  /**
   * Emit code for rule number 406:
   * r:      LONG_MUL(INT_2LONG(riv), INT_2LONG(riv))
   * @param p BURS node to apply the rule to
   */
  private void code406(AbstractBURS_TreeNode p) {
    INT_TO_LONG_MUL(P(p), Binary.getResult(P(p)), Unary.getVal(PL(p)), Unary.getVal(PR(p)), true);
  }

  /**
   * Emit code for rule number 407:
   * r:	LONG_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code407(AbstractBURS_TreeNode p) {
    EMIT_LongUnary(P(p), Unary.getResult(P(p)), Unary.getVal(P(p)), true);
  }

  /**
   * Emit code for rule number 408:
   * stm:	LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code408(AbstractBURS_TreeNode p) {
    EMIT_LongUnary(P(p), MO_S(P(p), QW), MO_S(P(p), QW), true);
  }

  /**
   * Emit code for rule number 409:
   * stm:	LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code409(AbstractBURS_TreeNode p) {
    EMIT_LongUnary(P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), true);
  }

  /**
   * Emit code for rule number 410:
   * r:	LONG_NOT(r)
   * @param p BURS node to apply the rule to
   */
  private void code410(AbstractBURS_TreeNode p) {
    EMIT_LongUnary(P(p), Unary.getResult(P(p)), Unary.getVal(P(p)), false);
  }

  /**
   * Emit code for rule number 411:
   * stm:	LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code411(AbstractBURS_TreeNode p) {
    EMIT_LongUnary(P(p), MO_S(P(p), QW), MO_S(P(p), QW), false);
  }

  /**
   * Emit code for rule number 412:
   * stm:	LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code412(AbstractBURS_TreeNode p) {
    EMIT_LongUnary(P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), false);
  }

  /**
   * Emit code for rule number 413:
   * r:	LONG_OR(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code413(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), Binary.getVal2(P(p)), true);
  }

  /**
   * Emit code for rule number 414:
   * r:	LONG_OR(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code414(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 415:
   * r:	LONG_OR(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code415(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), Binary.getResult(P(p)), Binary.getVal2(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 416:
   * stm:	LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code416(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 417:
   * stm:	LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code417(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 418:
   * stm:	LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code418(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 419:
   * stm:	LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code419(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_OR, IA32_OR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 420:
   * r:	LONG_SHL(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code420(AbstractBURS_TreeNode p) {
    LONG_SHL(P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)), false);
  }

  /**
   * Emit code for rule number 421:
   * r:	LONG_SHL(rlv, INT_AND(riv, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code421(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VRR(p) & 0x7FFFFFFF) <= 63); 
LONG_SHL(P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal1(PR(p)), true);
  }

  /**
   * Emit code for rule number 422:
   * r:	LONG_SHR(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code422(AbstractBURS_TreeNode p) {
    LONG_SHR(P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)), false);
  }

  /**
   * Emit code for rule number 423:
   * r:	LONG_SHR(rlv, INT_AND(riv, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code423(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VRR(p) & 0x7FFFFFFF) <= 63); 
LONG_SHR(P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal1(PR(p)), true);
  }

  /**
   * Emit code for rule number 424:
   * stm:	LONG_STORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code424(AbstractBURS_TreeNode p) {
    RegisterOperand hval = (RegisterOperand)Store.getClearValue(P(p)); 
hval.setType(TypeReference.Int); 
RegisterOperand lval = new RegisterOperand(regpool.getSecondReg(hval.getRegister()), TypeReference.Int); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_S(P(p), DW, DW).copy(), hval))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), DW), lval));
  }

  /**
   * Emit code for rule number 425:
   * stm:	LONG_STORE(LONG_CONSTANT, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code425(AbstractBURS_TreeNode p) {
    LongConstantOperand val = LC(Store.getClearValue(P(p))); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, MO_S(P(p), DW, DW).copy(), IC(val.upper32())))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), DW), IC(val.lower32())));
  }

  /**
   * Emit code for rule number 426:
   * r:	LONG_SUB(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code426(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_SUB, IA32_SBB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)), false);
  }

  /**
   * Emit code for rule number 427:
   * r:	LONG_SUB(rlv, load64)
   * @param p BURS node to apply the rule to
   */
  private void code427(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_SUB, IA32_SBB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO(), false);
  }

  /**
   * Emit code for rule number 428:
   * r:	LONG_SUB(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code428(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_SUB, IA32_SBB, P(p), Binary.getClearResult(P(p)),  consumeMO(), Binary.getClearVal2(P(p)), false);
  }

  /**
   * Emit code for rule number 429:
   * stm:	LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code429(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_SUB, IA32_SBB, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal2(PL(p)), false);
  }

  /**
   * Emit code for rule number 430:
   * stm:	LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code430(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_SUB, IA32_SBB, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p)), false);
  }

  /**
   * Emit code for rule number 431:
   * r:	LONG_USHR(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code431(AbstractBURS_TreeNode p) {
    LONG_USHR(P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)), false);
  }

  /**
   * Emit code for rule number 432:
   * r:	LONG_USHR(rlv, INT_AND(riv, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code432(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VRR(p) & 0x7FFFFFFF) <= 63); 
LONG_USHR(P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal1(PR(p)), true);
  }

  /**
   * Emit code for rule number 433:
   * r:	LONG_XOR(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code433(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), Binary.getVal2(P(p)), true);
  }

  /**
   * Emit code for rule number 434:
   * r:	LONG_XOR(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code434(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), Binary.getResult(P(p)), Binary.getVal1(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 435:
   * r:	LONG_XOR(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code435(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), Binary.getResult(P(p)), Binary.getVal2(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 436:
   * stm:	LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code436(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 437:
   * stm:	LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code437(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 438:
   * stm:	LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code438(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getVal2(PL(p)), true);
  }

  /**
   * Emit code for rule number 439:
   * stm:	LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code439(AbstractBURS_TreeNode p) {
    EMIT_LongBinary(IA32_XOR, IA32_XOR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getVal1(PL(p)), true);
  }

  /**
   * Emit code for rule number 440:
   * r: FLOAT_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code440(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 441:
   * r: FLOAT_ADD(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code441(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 442:
   * r: FLOAT_ADD(float_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code442(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 443:
   * r: DOUBLE_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code443(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), Binary.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 444:
   * r: DOUBLE_ADD(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code444(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 445:
   * r: DOUBLE_ADD(double_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code445(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 446:
   * r: FLOAT_SUB(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code446(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 447:
   * r: FLOAT_SUB(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code447(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 448:
   * r: DOUBLE_SUB(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code448(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 449:
   * r: DOUBLE_SUB(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code449(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 450:
   * r: FLOAT_MUL(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code450(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 451:
   * r: FLOAT_MUL(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code451(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 452:
   * r: FLOAT_MUL(float_load, r)
   * @param p BURS node to apply the rule to
   */
  private void code452(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 453:
   * r: DOUBLE_MUL(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code453(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 454:
   * r: DOUBLE_MUL(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code454(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 455:
   * r: DOUBLE_MUL(double_load, r)
   * @param p BURS node to apply the rule to
   */
  private void code455(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 456:
   * r: FLOAT_DIV(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code456(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 457:
   * r: FLOAT_DIV(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code457(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 458:
   * r: DOUBLE_DIV(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code458(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 459:
   * r: DOUBLE_DIV(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code459(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 460:
   * r: FLOAT_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code460(AbstractBURS_TreeNode p) {
    SSE2_NEG(true, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 461:
   * r: DOUBLE_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code461(AbstractBURS_TreeNode p) {
    SSE2_NEG(false, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 462:
   * r: FLOAT_SQRT(r)
   * @param p BURS node to apply the rule to
   */
  private void code462(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_SQRTSS, Unary.getClearResult(P(p)), Unary.getClearVal(P(p))));
  }

  /**
   * Emit code for rule number 463:
   * r: DOUBLE_SQRT(r)
   * @param p BURS node to apply the rule to
   */
  private void code463(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_SQRTSD, Unary.getClearResult(P(p)), Unary.getClearVal(P(p))));
  }

  /**
   * Emit code for rule number 464:
   * r: FLOAT_REM(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code464(AbstractBURS_TreeNode p) {
    SSE2_X87_REM(P(p));
  }

  /**
   * Emit code for rule number 465:
   * r: DOUBLE_REM(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code465(AbstractBURS_TreeNode p) {
    SSE2_X87_REM(P(p));
  }

  /**
   * Emit code for rule number 466:
   * r: LONG_2FLOAT(r)
   * @param p BURS node to apply the rule to
   */
  private void code466(AbstractBURS_TreeNode p) {
    SSE2_X87_FROMLONG(P(p));
  }

  /**
   * Emit code for rule number 467:
   * r: LONG_2DOUBLE(r)
   * @param p BURS node to apply the rule to
   */
  private void code467(AbstractBURS_TreeNode p) {
    SSE2_X87_FROMLONG(P(p));
  }

  /**
   * Emit code for rule number 468:
   * r: FLOAT_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code468(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVAPS, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 469:
   * r: DOUBLE_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code469(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVAPD, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 470:
   * r: DOUBLE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code470(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 471:
   * r: DOUBLE_LOAD(riv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code471(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 472:
   * r: DOUBLE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code472(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 473:
   * double_load: DOUBLE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code473(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), QW));
  }

  /**
   * Emit code for rule number 474:
   * r: DOUBLE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code474(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 475:
   * r: DOUBLE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code475(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 476:
   * double_load: DOUBLE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code476(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), QW));
  }

  /**
   * Emit code for rule number 477:
   * r: DOUBLE_ALOAD(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code477(AbstractBURS_TreeNode p) {
    RegisterOperand index=ALoad.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
}
  }

  /**
   * Emit code for rule number 478:
   * r: DOUBLE_ALOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code478(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 479:
   * double_load: DOUBLE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code479(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 480:
   * double_load: DOUBLE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code480(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 481:
   * r: FLOAT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code481(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, Load.getResult(P(p)), MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 482:
   * r: FLOAT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code482(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, Load.getResult(P(p)), MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 483:
   * float_load: FLOAT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code483(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), DW));
  }

  /**
   * Emit code for rule number 484:
   * float_load: FLOAT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code484(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 485:
   * r: FLOAT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code485(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 486:
   * r: FLOAT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code486(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 487:
   * r: FLOAT_ALOAD(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code487(AbstractBURS_TreeNode p) {
    RegisterOperand index=ALoad.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
}
  }

  /**
   * Emit code for rule number 488:
   * r: FLOAT_ALOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code488(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 489:
   * float_load: FLOAT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code489(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 490:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code490(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 491:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code491(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 492:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code492(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 493:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code493(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 494:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code494(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 495:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code495(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 496:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code496(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 497:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code497(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 498:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code498(AbstractBURS_TreeNode p) {
    RegisterOperand index=AStore.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 499:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code499(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 500:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code500(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 501:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code501(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 502:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code502(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 503:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code503(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 504:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code504(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 505:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code505(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 506:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code506(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 507:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code507(AbstractBURS_TreeNode p) {
    RegisterOperand index=AStore.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 508:
   * r: INT_2FLOAT(riv)
   * @param p BURS node to apply the rule to
   */
  private void code508(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SS, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 509:
   * r: INT_2FLOAT(load32)
   * @param p BURS node to apply the rule to
   */
  private void code509(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SS, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 510:
   * r: INT_2DOUBLE(riv)
   * @param p BURS node to apply the rule to
   */
  private void code510(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SD, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 511:
   * r: INT_2DOUBLE(load32)
   * @param p BURS node to apply the rule to
   */
  private void code511(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SD, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 512:
   * r: FLOAT_2DOUBLE(r)
   * @param p BURS node to apply the rule to
   */
  private void code512(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSS2SD, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 513:
   * r: FLOAT_2DOUBLE(float_load)
   * @param p BURS node to apply the rule to
   */
  private void code513(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSS2SD, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 514:
   * r: DOUBLE_2FLOAT(r)
   * @param p BURS node to apply the rule to
   */
  private void code514(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSD2SS, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 515:
   * r: DOUBLE_2FLOAT(double_load)
   * @param p BURS node to apply the rule to
   */
  private void code515(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSD2SS, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 516:
   * r: FLOAT_2INT(r)
   * @param p BURS node to apply the rule to
   */
  private void code516(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 517:
   * r: FLOAT_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code517(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 518:
   * r: DOUBLE_2INT(r)
   * @param p BURS node to apply the rule to
   */
  private void code518(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 519:
   * r: DOUBLE_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code519(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 520:
   * r: FLOAT_AS_INT_BITS(r)
   * @param p BURS node to apply the rule to
   */
  private void code520(AbstractBURS_TreeNode p) {
    SSE2_FPR2GPR_32(P(p));
  }

  /**
   * Emit code for rule number 522:
   * r: DOUBLE_AS_LONG_BITS(r)
   * @param p BURS node to apply the rule to
   */
  private void code522(AbstractBURS_TreeNode p) {
    SSE2_FPR2GPR_64(P(p));
  }

  /**
   * Emit code for rule number 524:
   * r: INT_BITS_AS_FLOAT(riv)
   * @param p BURS node to apply the rule to
   */
  private void code524(AbstractBURS_TreeNode p) {
    SSE2_GPR2FPR_32(P(p));
  }

  /**
   * Emit code for rule number 526:
   * r: LONG_BITS_AS_DOUBLE(rlv)
   * @param p BURS node to apply the rule to
   */
  private void code526(AbstractBURS_TreeNode p) {
    SSE2_GPR2FPR_64(P(p));
  }

  /**
   * Emit code for rule number 528:
   * r: MATERIALIZE_FP_CONSTANT(any)
   * @param p BURS node to apply the rule to
   */
  private void code528(AbstractBURS_TreeNode p) {
    SSE2_FPCONSTANT(P(p));
  }

  /**
   * Emit code for rule number 529:
   * float_load: MATERIALIZE_FP_CONSTANT(any)
   * @param p BURS node to apply the rule to
   */
  private void code529(AbstractBURS_TreeNode p) {
    pushMO(MO_MC(P(p)));
  }

  /**
   * Emit code for rule number 530:
   * double_load: MATERIALIZE_FP_CONSTANT(any)
   * @param p BURS node to apply the rule to
   */
  private void code530(AbstractBURS_TreeNode p) {
    pushMO(MO_MC(P(p)));
  }

  /**
   * Emit code for rule number 531:
   * stm: CLEAR_FLOATING_POINT_STATE
   * @param p BURS node to apply the rule to
   */
  private void code531(AbstractBURS_TreeNode p) {
    EMIT(MIR_Empty.mutate(P(p), IA32_FNINIT));
  }

  /**
   * Emit code for rule number 532:
   * stm: FLOAT_IFCMP(r,r)
   * @param p BURS node to apply the rule to
   */
  private void code532(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISS, P(p), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 533:
   * stm: FLOAT_IFCMP(r,float_load)
   * @param p BURS node to apply the rule to
   */
  private void code533(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISS, P(p), IfCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 534:
   * stm: FLOAT_IFCMP(float_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code534(AbstractBURS_TreeNode p) {
    IfCmp.getCond(P(p)).flipOperands(); SSE2_IFCMP(IA32_UCOMISS, P(p), IfCmp.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 535:
   * stm: DOUBLE_IFCMP(r,r)
   * @param p BURS node to apply the rule to
   */
  private void code535(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISD, P(p), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 536:
   * stm: DOUBLE_IFCMP(r,double_load)
   * @param p BURS node to apply the rule to
   */
  private void code536(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISD, P(p), IfCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 537:
   * stm: DOUBLE_IFCMP(double_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code537(AbstractBURS_TreeNode p) {
    IfCmp.getCond(P(p)).flipOperands(); SSE2_IFCMP(IA32_UCOMISD, P(p), IfCmp.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 538:
   * r: FCMP_CMOV(r, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code538(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(CondMove.getVal1(P(p)).isFloat() ? IA32_UCOMISS : IA32_UCOMISD,      CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p))))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 539:
   * r: FCMP_CMOV(r, OTHER_OPERAND(float_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code539(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISS, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 540:
   * r: FCMP_CMOV(r, OTHER_OPERAND(double_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code540(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISD, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 541:
   * r: FCMP_CMOV(float_load, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code541(AbstractBURS_TreeNode p) {
    CondMove.getCond(P(p)).flipOperands(); EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISS, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 542:
   * r: FCMP_CMOV(double_load, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code542(AbstractBURS_TreeNode p) {
    CondMove.getCond(P(p)).flipOperands(); EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISD, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 543:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code543(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 544:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, float_load)))
   * @param p BURS node to apply the rule to
   */
  private void code544(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), CondMove.getClearTrueValue(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 545:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, double_load)))
   * @param p BURS node to apply the rule to
   */
  private void code545(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), CondMove.getClearTrueValue(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 546:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(float_load, r)))
   * @param p BURS node to apply the rule to
   */
  private void code546(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), consumeMO(), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 547:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(double_load, r)))
   * @param p BURS node to apply the rule to
   */
  private void code547(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), consumeMO(), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 548:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(float_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code548(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), consumeMO(),                 CondMove.getClearCond(P(p)), CondMove.getClearFalseValue(P(p)), CondMove.getClearTrueValue(P(p)));
  }

  /**
   * Emit code for rule number 549:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(double_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code549(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), consumeMO(),                 CondMove.getClearCond(P(p)), CondMove.getClearFalseValue(P(p)), CondMove.getClearTrueValue(P(p)));
  }

  /**
   * Emit code for rule number 550:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code550(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 551:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code551(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 552:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code552(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 553:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code553(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 554:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code554(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 555:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code555(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 556:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code556(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 557:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code557(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 558:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code558(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 559:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code559(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 560:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code560(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 561:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code561(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 562:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code562(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 563:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code563(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 564:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code564(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 565:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code565(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 566:
   * stm: LONG_ASTORE(load64, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code566(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_AS(P(p), QW_S, QW), temp.copyRO()));
  }

  /**
   * Emit code for rule number 567:
   * stm: LONG_ASTORE(load64, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code567(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_AS(P(p), QW_S, QW), temp.copyRO()));
  }

  /**
   * Emit code for rule number 568:
   * stm: LONG_STORE(load64, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code568(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_S(P(p), QW), temp.copyRO()));
  }

  /**
   * Emit code for rule number 569:
   * stm: LONG_STORE(load64, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code569(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_S(P(p), QW), temp.copyRO()));
  }

  /**
   * Emit code using given rule number
   *
   * @param p the tree that's being emitted
   * @param n the non-terminal goal of that tree
   * @param ruleno the rule that will generate the tree
   */
    @Override
  public void code(AbstractBURS_TreeNode p, int  n, int ruleno) {
    switch(unsortedErnMap[ruleno]) {
    case 16: code16(p); break;
    case 17: code17(p); break;
    case 18: code18(p); break;
    case 19: code19(p); break;
    case 20: code20(p); break;
    case 21: code21(p); break;
    case 22: code22(p); break;
    case 23: code23(p); break;
    case 24: code24(p); break;
    case 26: code26(p); break;
    case 27: code27(p); break;
    case 28: code28(p); break;
    case 29: code29(p); break;
    case 30: code30(p); break;
    case 31: code31(p); break;
    case 32: code32(p); break;
    case 33: code33(p); break;
    case 34: code34(p); break;
    case 35: code35(p); break;
    case 36: code36(p); break;
    case 37: code37(p); break;
    case 38: code38(p); break;
    case 39: code39(p); break;
    case 40: code40(p); break;
    case 41: code41(p); break;
    case 42: code42(p); break;
    case 43: code43(p); break;
    case 44: code44(p); break;
    case 45: code45(p); break;
    case 46: code46(p); break;
    case 47: code47(p); break;
    case 48: code48(p); break;
    case 49: code49(p); break;
    case 50: code50(p); break;
    case 51: code51(p); break;
    case 52: code52(p); break;
    case 53: code53(p); break;
    case 54: code54(p); break;
    case 55: code55(p); break;
    case 56: code56(p); break;
    case 57: code57(p); break;
    case 58: code58(p); break;
    case 59: code59(p); break;
    case 60: code60(p); break;
    case 61: code61(p); break;
    case 62: code62(p); break;
    case 63: code63(p); break;
    case 64: code64(p); break;
    case 65: code65(p); break;
    case 66: code66(p); break;
    case 67: code67(p); break;
    case 68: code68(p); break;
    case 69: code69(p); break;
    case 70: code70(p); break;
    case 71: code71(p); break;
    case 72: code72(p); break;
    case 73: code73(p); break;
    case 74: code74(p); break;
    case 75: code75(p); break;
    case 76: code76(p); break;
    case 77: code77(p); break;
    case 78: code78(p); break;
    case 79: code79(p); break;
    case 80: code80(p); break;
    case 81: code81(p); break;
    case 82: code82(p); break;
    case 83: code83(p); break;
    case 84: code84(p); break;
    case 87: code87(p); break;
    case 88: code88(p); break;
    case 89: code89(p); break;
    case 90: code90(p); break;
    case 91: code91(p); break;
    case 92: code92(p); break;
    case 93: code93(p); break;
    case 94: code94(p); break;
    case 96: code96(p); break;
    case 99: code99(p); break;
    case 100: code100(p); break;
    case 101: code101(p); break;
    case 102: code102(p); break;
    case 103: code103(p); break;
    case 104: code104(p); break;
    case 105: code105(p); break;
    case 106: code106(p); break;
    case 107: code107(p); break;
    case 108: code108(p); break;
    case 109: code109(p); break;
    case 110: code110(p); break;
    case 111: code111(p); break;
    case 112: code112(p); break;
    case 113: code113(p); break;
    case 114: code114(p); break;
    case 115: code115(p); break;
    case 116: code116(p); break;
    case 117: code117(p); break;
    case 118: code118(p); break;
    case 119: code119(p); break;
    case 120: code120(p); break;
    case 121: code121(p); break;
    case 122: code122(p); break;
    case 123: code123(p); break;
    case 124: code124(p); break;
    case 125: code125(p); break;
    case 126: code126(p); break;
    case 127: code127(p); break;
    case 128: code128(p); break;
    case 129: code129(p); break;
    case 130: code130(p); break;
    case 131: code131(p); break;
    case 132: code132(p); break;
    case 133: code133(p); break;
    case 134: code134(p); break;
    case 135: code135(p); break;
    case 136: code136(p); break;
    case 137: code137(p); break;
    case 138: code138(p); break;
    case 139: code139(p); break;
    case 140: code140(p); break;
    case 141: code141(p); break;
    case 142: code142(p); break;
    case 143: code143(p); break;
    case 144: code144(p); break;
    case 145: code145(p); break;
    case 146: code146(p); break;
    case 147: code147(p); break;
    case 148: code148(p); break;
    case 149: code149(p); break;
    case 150: code150(p); break;
    case 151: code151(p); break;
    case 153: code153(p); break;
    case 154: code154(p); break;
    case 155: code155(p); break;
    case 156: code156(p); break;
    case 157: code157(p); break;
    case 158: code158(p); break;
    case 159: code159(p); break;
    case 160: code160(p); break;
    case 161: code161(p); break;
    case 162: code162(p); break;
    case 163: code163(p); break;
    case 164: code164(p); break;
    case 165: code165(p); break;
    case 166: code166(p); break;
    case 167: code167(p); break;
    case 168: code168(p); break;
    case 169: code169(p); break;
    case 170: code170(p); break;
    case 171: code171(p); break;
    case 172: code172(p); break;
    case 173: code173(p); break;
    case 174: code174(p); break;
    case 175: code175(p); break;
    case 176: code176(p); break;
    case 177: code177(p); break;
    case 178: code178(p); break;
    case 179: code179(p); break;
    case 180: code180(p); break;
    case 181: code181(p); break;
    case 182: code182(p); break;
    case 183: code183(p); break;
    case 184: code184(p); break;
    case 185: code185(p); break;
    case 186: code186(p); break;
    case 187: code187(p); break;
    case 188: code188(p); break;
    case 189: code189(p); break;
    case 190: code190(p); break;
    case 191: code191(p); break;
    case 192: code192(p); break;
    case 193: code193(p); break;
    case 194: code194(p); break;
    case 195: code195(p); break;
    case 196: code196(p); break;
    case 197: code197(p); break;
    case 198: code198(p); break;
    case 199: code199(p); break;
    case 200: code200(p); break;
    case 201: code201(p); break;
    case 202: code202(p); break;
    case 203: code203(p); break;
    case 204: code204(p); break;
    case 205: code205(p); break;
    case 206: code206(p); break;
    case 207: code207(p); break;
    case 208: code208(p); break;
    case 209: code209(p); break;
    case 210: code210(p); break;
    case 211: code211(p); break;
    case 212: code212(p); break;
    case 213: code213(p); break;
    case 214: code214(p); break;
    case 215: code215(p); break;
    case 216: code216(p); break;
    case 217: code217(p); break;
    case 218: code218(p); break;
    case 219: code219(p); break;
    case 220: code220(p); break;
    case 221: code221(p); break;
    case 222: code222(p); break;
    case 223: code223(p); break;
    case 224: code224(p); break;
    case 225: code225(p); break;
    case 226: code226(p); break;
    case 227: code227(p); break;
    case 228: code228(p); break;
    case 229: code229(p); break;
    case 230: code230(p); break;
    case 231: code231(p); break;
    case 232: code232(p); break;
    case 233: code233(p); break;
    case 234: code234(p); break;
    case 235: code235(p); break;
    case 236: code236(p); break;
    case 237: code237(p); break;
    case 238: code238(p); break;
    case 239: code239(p); break;
    case 240: code240(p); break;
    case 241: code241(p); break;
    case 242: code242(p); break;
    case 243: code243(p); break;
    case 244: code244(p); break;
    case 245: code245(p); break;
    case 246: code246(p); break;
    case 247: code247(p); break;
    case 248: code248(p); break;
    case 249: code249(p); break;
    case 250: code250(p); break;
    case 251: code251(p); break;
    case 252: code252(p); break;
    case 253: code253(p); break;
    case 255: code255(p); break;
    case 264: code264(p); break;
    case 265: code265(p); break;
    case 266: code266(p); break;
    case 267: code267(p); break;
    case 268: code268(p); break;
    case 269: code269(p); break;
    case 270: code270(p); break;
    case 271: code271(p); break;
    case 272: code272(p); break;
    case 273: code273(p); break;
    case 274: code274(p); break;
    case 275: code275(p); break;
    case 276: code276(p); break;
    case 277: code277(p); break;
    case 278: code278(p); break;
    case 279: code279(p); break;
    case 280: code280(p); break;
    case 281: code281(p); break;
    case 282: code282(p); break;
    case 283: code283(p); break;
    case 284: code284(p); break;
    case 285: code285(p); break;
    case 286: code286(p); break;
    case 287: code287(p); break;
    case 288: code288(p); break;
    case 289: code289(p); break;
    case 290: code290(p); break;
    case 291: code291(p); break;
    case 292: code292(p); break;
    case 293: code293(p); break;
    case 294: code294(p); break;
    case 295: code295(p); break;
    case 296: code296(p); break;
    case 297: code297(p); break;
    case 298: code298(p); break;
    case 299: code299(p); break;
    case 300: code300(p); break;
    case 301: code301(p); break;
    case 302: code302(p); break;
    case 303: code303(p); break;
    case 304: code304(p); break;
    case 305: code305(p); break;
    case 306: code306(p); break;
    case 307: code307(p); break;
    case 308: code308(p); break;
    case 309: code309(p); break;
    case 310: code310(p); break;
    case 311: code311(p); break;
    case 312: code312(p); break;
    case 313: code313(p); break;
    case 314: code314(p); break;
    case 315: code315(p); break;
    case 316: code316(p); break;
    case 317: code317(p); break;
    case 318: code318(p); break;
    case 319: code319(p); break;
    case 320: code320(p); break;
    case 321: code321(p); break;
    case 322: code322(p); break;
    case 323: code323(p); break;
    case 324: code324(p); break;
    case 325: code325(p); break;
    case 326: code326(p); break;
    case 327: code327(p); break;
    case 328: code328(p); break;
    case 329: code329(p); break;
    case 330: code330(p); break;
    case 331: code331(p); break;
    case 332: code332(p); break;
    case 333: code333(p); break;
    case 334: code334(p); break;
    case 335: code335(p); break;
    case 336: code336(p); break;
    case 337: code337(p); break;
    case 338: code338(p); break;
    case 339: code339(p); break;
    case 340: code340(p); break;
    case 341: code341(p); break;
    case 342: code342(p); break;
    case 343: code343(p); break;
    case 344: code344(p); break;
    case 345: code345(p); break;
    case 346: code346(p); break;
    case 347: code347(p); break;
    case 348: code348(p); break;
    case 349: code349(p); break;
    case 350: code350(p); break;
    case 351: code351(p); break;
    case 354: code354(p); break;
    case 355: code355(p); break;
    case 356: code356(p); break;
    case 357: code357(p); break;
    case 358: code358(p); break;
    case 359: code359(p); break;
    case 360: code360(p); break;
    case 361: code361(p); break;
    case 364: code364(p); break;
    case 365: code365(p); break;
    case 370: code370(p); break;
    case 371: code371(p); break;
    case 372: code372(p); break;
    case 373: code373(p); break;
    case 374: code374(p); break;
    case 375: code375(p); break;
    case 376: code376(p); break;
    case 377: code377(p); break;
    case 378: code378(p); break;
    case 379: code379(p); break;
    case 380: code380(p); break;
    case 381: code381(p); break;
    case 382: code382(p); break;
    case 383: code383(p); break;
    case 384: code384(p); break;
    case 385: code385(p); break;
    case 386: code386(p); break;
    case 387: code387(p); break;
    case 388: code388(p); break;
    case 389: code389(p); break;
    case 390: code390(p); break;
    case 391: code391(p); break;
    case 392: code392(p); break;
    case 393: code393(p); break;
    case 394: code394(p); break;
    case 395: code395(p); break;
    case 396: code396(p); break;
    case 397: code397(p); break;
    case 398: code398(p); break;
    case 399: code399(p); break;
    case 400: code400(p); break;
    case 401: code401(p); break;
    case 403: code403(p); break;
    case 404: code404(p); break;
    case 405: code405(p); break;
    case 406: code406(p); break;
    case 407: code407(p); break;
    case 408: code408(p); break;
    case 409: code409(p); break;
    case 410: code410(p); break;
    case 411: code411(p); break;
    case 412: code412(p); break;
    case 413: code413(p); break;
    case 414: code414(p); break;
    case 415: code415(p); break;
    case 416: code416(p); break;
    case 417: code417(p); break;
    case 418: code418(p); break;
    case 419: code419(p); break;
    case 420: code420(p); break;
    case 421: code421(p); break;
    case 422: code422(p); break;
    case 423: code423(p); break;
    case 424: code424(p); break;
    case 425: code425(p); break;
    case 426: code426(p); break;
    case 427: code427(p); break;
    case 428: code428(p); break;
    case 429: code429(p); break;
    case 430: code430(p); break;
    case 431: code431(p); break;
    case 432: code432(p); break;
    case 433: code433(p); break;
    case 434: code434(p); break;
    case 435: code435(p); break;
    case 436: code436(p); break;
    case 437: code437(p); break;
    case 438: code438(p); break;
    case 439: code439(p); break;
    case 440: code440(p); break;
    case 441: code441(p); break;
    case 442: code442(p); break;
    case 443: code443(p); break;
    case 444: code444(p); break;
    case 445: code445(p); break;
    case 446: code446(p); break;
    case 447: code447(p); break;
    case 448: code448(p); break;
    case 449: code449(p); break;
    case 450: code450(p); break;
    case 451: code451(p); break;
    case 452: code452(p); break;
    case 453: code453(p); break;
    case 454: code454(p); break;
    case 455: code455(p); break;
    case 456: code456(p); break;
    case 457: code457(p); break;
    case 458: code458(p); break;
    case 459: code459(p); break;
    case 460: code460(p); break;
    case 461: code461(p); break;
    case 462: code462(p); break;
    case 463: code463(p); break;
    case 464: code464(p); break;
    case 465: code465(p); break;
    case 466: code466(p); break;
    case 467: code467(p); break;
    case 468: code468(p); break;
    case 469: code469(p); break;
    case 470: code470(p); break;
    case 471: code471(p); break;
    case 472: code472(p); break;
    case 473: code473(p); break;
    case 474: code474(p); break;
    case 475: code475(p); break;
    case 476: code476(p); break;
    case 477: code477(p); break;
    case 478: code478(p); break;
    case 479: code479(p); break;
    case 480: code480(p); break;
    case 481: code481(p); break;
    case 482: code482(p); break;
    case 483: code483(p); break;
    case 484: code484(p); break;
    case 485: code485(p); break;
    case 486: code486(p); break;
    case 487: code487(p); break;
    case 488: code488(p); break;
    case 489: code489(p); break;
    case 490: code490(p); break;
    case 491: code491(p); break;
    case 492: code492(p); break;
    case 493: code493(p); break;
    case 494: code494(p); break;
    case 495: code495(p); break;
    case 496: code496(p); break;
    case 497: code497(p); break;
    case 498: code498(p); break;
    case 499: code499(p); break;
    case 500: code500(p); break;
    case 501: code501(p); break;
    case 502: code502(p); break;
    case 503: code503(p); break;
    case 504: code504(p); break;
    case 505: code505(p); break;
    case 506: code506(p); break;
    case 507: code507(p); break;
    case 508: code508(p); break;
    case 509: code509(p); break;
    case 510: code510(p); break;
    case 511: code511(p); break;
    case 512: code512(p); break;
    case 513: code513(p); break;
    case 514: code514(p); break;
    case 515: code515(p); break;
    case 516: code516(p); break;
    case 517: code517(p); break;
    case 518: code518(p); break;
    case 519: code519(p); break;
    case 520: code520(p); break;
    case 522: code522(p); break;
    case 524: code524(p); break;
    case 526: code526(p); break;
    case 528: code528(p); break;
    case 529: code529(p); break;
    case 530: code530(p); break;
    case 531: code531(p); break;
    case 532: code532(p); break;
    case 533: code533(p); break;
    case 534: code534(p); break;
    case 535: code535(p); break;
    case 536: code536(p); break;
    case 537: code537(p); break;
    case 538: code538(p); break;
    case 539: code539(p); break;
    case 540: code540(p); break;
    case 541: code541(p); break;
    case 542: code542(p); break;
    case 543: code543(p); break;
    case 544: code544(p); break;
    case 545: code545(p); break;
    case 546: code546(p); break;
    case 547: code547(p); break;
    case 548: code548(p); break;
    case 549: code549(p); break;
    case 550: code550(p); break;
    case 551: code551(p); break;
    case 552: code552(p); break;
    case 553: code553(p); break;
    case 554: code554(p); break;
    case 555: code555(p); break;
    case 556: code556(p); break;
    case 557: code557(p); break;
    case 558: code558(p); break;
    case 559: code559(p); break;
    case 560: code560(p); break;
    case 561: code561(p); break;
    case 562: code562(p); break;
    case 563: code563(p); break;
    case 564: code564(p); break;
    case 565: code565(p); break;
    case 566: code566(p); break;
    case 567: code567(p); break;
    case 568: code568(p); break;
    case 569: code569(p); break;
    default:
      throw new OptimizingCompilerException("BURS", "rule " + ruleno + " without emit code:",
        BURS_Debug.string[unsortedErnMap[ruleno]]);
    }
  }
}
