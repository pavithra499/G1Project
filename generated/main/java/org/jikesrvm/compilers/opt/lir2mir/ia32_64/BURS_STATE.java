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
package org.jikesrvm.compilers.opt.lir2mir.ia32_64;

import static org.jikesrvm.compilers.opt.ir.Operators.*;
import static org.jikesrvm.compilers.opt.ir.ia32.ArchOperators.*;
import static org.jikesrvm.compilers.opt.lir2mir.ia32_64.BURS_Definitions.*;
import static org.jikesrvm.compilers.opt.ir.IRTools.*;

import org.jikesrvm.*;
import org.jikesrvm.classloader.*;
import org.jikesrvm.compilers.opt.ir.*;
import org.jikesrvm.compilers.opt.ir.ia32.*;
import org.jikesrvm.compilers.opt.ir.operand.*;
import org.jikesrvm.compilers.opt.ir.operand.ia32.*;
import org.jikesrvm.compilers.opt.lir2mir.ia32.BURS_Helpers;
import org.jikesrvm.compilers.opt.lir2mir.ia32_64.BURS_TreeNode;
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
    85, /* 9 - address1scaledreg: address1reg */
    86, /* 10 - address: address1scaledreg */
    393, /* 11 - load8: sload8 */
    394, /* 12 - load8: uload8 */
    405, /* 13 - load16: sload16 */
    406, /* 14 - load16: uload16 */
    409, /* 15 - load16_32: load16 */
    410, /* 16 - load16_32: load32 */
    411, /* 17 - load8_16_32: load16_32 */
    412, /* 18 - load8_16_32: load8 */
    416, /* 19 - load8_16_32_64: load64 */
    417, /* 20 - load8_16_32_64: load8_16_32 */
    2, /* 21 - r: REGISTER */
    8, /* 22 - riv: INT_CONSTANT */
    10, /* 23 - rlv: LONG_CONSTANT */
    11, /* 24 - any: NULL */
    13, /* 25 - any: ADDRESS_CONSTANT */
    14, /* 26 - any: LONG_CONSTANT */
    16, /* 27 - stm: IG_PATCH_POINT */
    17, /* 28 - stm: UNINT_BEGIN */
    18, /* 29 - stm: UNINT_END */
    19, /* 30 - stm: YIELDPOINT_PROLOGUE */
    20, /* 31 - stm: YIELDPOINT_EPILOGUE */
    21, /* 32 - stm: YIELDPOINT_BACKEDGE */
    22, /* 33 - r: FRAMESIZE */
    24, /* 34 - stm: RESOLVE */
    25, /* 35 - stm: NOP */
    26, /* 36 - r: GUARD_MOVE */
    27, /* 37 - r: GUARD_COMBINE */
    29, /* 38 - stm: IR_PROLOGUE */
    30, /* 39 - r: GET_CAUGHT_EXCEPTION */
    32, /* 40 - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT) */
    33, /* 41 - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT) */
    34, /* 42 - stm: TRAP */
    64, /* 43 - stm: GOTO */
    66, /* 44 - stm: WRITE_FLOOR */
    67, /* 45 - stm: READ_CEILING */
    68, /* 46 - stm: FENCE */
    69, /* 47 - stm: PAUSE */
    70, /* 48 - stm: ILLEGAL_INSTRUCTION */
    71, /* 49 - stm: RETURN(NULL) */
    72, /* 50 - stm: RETURN(INT_CONSTANT) */
    74, /* 51 - stm: RETURN(LONG_CONSTANT) */
    83, /* 52 - r: GET_TIME_BASE */
    625, /* 53 - stm: CLEAR_FLOATING_POINT_STATE */
    15, /* 54 - any: OTHER_OPERAND(any,any) */
    37, /* 55 - stm: TRAP_IF(r,r) */
    38, /* 56 - stm: TRAP_IF(load32,riv) */
    39, /* 57 - stm: TRAP_IF(riv,load32) */
    63, /* 58 - r: LONG_CMP(rlv,rlv) */
    75, /* 59 - r: CALL(r,any) */
    80, /* 60 - r: SYSCALL(r,any) */
    84, /* 61 - stm: YIELDPOINT_OSR(any,any) */
    90, /* 62 - address: INT_ADD(r,r) */
    93, /* 63 - address: INT_ADD(r,address1scaledreg) */
    94, /* 64 - address: INT_ADD(address1scaledreg,r) */
    96, /* 65 - address: INT_ADD(address1scaledreg,address1reg) */
    97, /* 66 - address: INT_ADD(address1reg,address1scaledreg) */
    101, /* 67 - address: LONG_ADD(r,r) */
    104, /* 68 - address: LONG_ADD(r,address1scaledreg) */
    105, /* 69 - address: LONG_ADD(address1scaledreg,r) */
    107, /* 70 - address: LONG_ADD(address1scaledreg,address1reg) */
    108, /* 71 - address: LONG_ADD(address1reg,address1scaledreg) */
    163, /* 72 - r: BOOLEAN_CMP_INT(r,riv) */
    164, /* 73 - boolcmp: BOOLEAN_CMP_INT(r,riv) */
    181, /* 74 - r: BOOLEAN_CMP_INT(load32,riv) */
    182, /* 75 - boolcmp: BOOLEAN_CMP_INT(load32,riv) */
    183, /* 76 - r: BOOLEAN_CMP_INT(r,load32) */
    184, /* 77 - boolcmp: BOOLEAN_CMP_INT(riv,load32) */
    187, /* 78 - r: BOOLEAN_CMP_LONG(r,rlv) */
    188, /* 79 - boolcmp: BOOLEAN_CMP_LONG(r,rlv) */
    196, /* 80 - r: BOOLEAN_CMP_LONG(load64,rlv) */
    197, /* 81 - boolcmp: BOOLEAN_CMP_LONG(load64,rlv) */
    198, /* 82 - r: BOOLEAN_CMP_LONG(r,load64) */
    199, /* 83 - boolcmp: BOOLEAN_CMP_LONG(rlv,load64) */
    243, /* 84 - czr: INT_ADD(r,riv) */
    244, /* 85 - r: INT_ADD(r,riv) */
    245, /* 86 - czr: INT_ADD(r,load32) */
    246, /* 87 - czr: INT_ADD(load32,riv) */
    251, /* 88 - szpr: INT_AND(r,riv) */
    252, /* 89 - szp: INT_AND(r,riv) */
    253, /* 90 - szpr: INT_AND(r,load32) */
    254, /* 91 - szpr: INT_AND(load32,riv) */
    255, /* 92 - szp: INT_AND(load8_16_32,riv) */
    256, /* 93 - szp: INT_AND(r,load8_16_32) */
    261, /* 94 - r: INT_DIV(riv,riv) */
    262, /* 95 - r: INT_DIV(riv,load32) */
    263, /* 96 - r: UNSIGNED_DIV_64_32(rlv,riv) */
    264, /* 97 - r: UNSIGNED_DIV_64_32(rlv,load32) */
    265, /* 98 - stm: INT_IFCMP(r,riv) */
    268, /* 99 - stm: INT_IFCMP(uload8,r) */
    269, /* 100 - stm: INT_IFCMP(r,uload8) */
    271, /* 101 - stm: INT_IFCMP(load32,riv) */
    272, /* 102 - stm: INT_IFCMP(r,load32) */
    278, /* 103 - stm: INT_IFCMP2(r,riv) */
    279, /* 104 - stm: INT_IFCMP2(load32,riv) */
    280, /* 105 - stm: INT_IFCMP2(riv,load32) */
    281, /* 106 - r: INT_LOAD(rlv,rlv) */
    282, /* 107 - r: INT_LOAD(rlv,address1scaledreg) */
    283, /* 108 - r: INT_LOAD(address1scaledreg,rlv) */
    284, /* 109 - r: INT_LOAD(address1scaledreg,address1reg) */
    285, /* 110 - r: INT_LOAD(address1reg,address1scaledreg) */
    287, /* 111 - r: INT_ALOAD(rlv,riv) */
    300, /* 112 - r: INT_MUL(r,riv) */
    301, /* 113 - r: INT_MUL(r,load32) */
    302, /* 114 - r: INT_MUL(load32,riv) */
    309, /* 115 - szpr: INT_OR(r,riv) */
    310, /* 116 - szpr: INT_OR(r,load32) */
    311, /* 117 - szpr: INT_OR(load32,riv) */
    316, /* 118 - r: INT_REM(riv,riv) */
    317, /* 119 - r: INT_REM(riv,load32) */
    318, /* 120 - r: UNSIGNED_REM_64_32(rlv,riv) */
    319, /* 121 - r: UNSIGNED_REM_64_32(rlv,load32) */
    329, /* 122 - szpr: INT_SHL(riv,riv) */
    338, /* 123 - szpr: INT_SHR(riv,riv) */
    350, /* 124 - czr: INT_SUB(riv,r) */
    351, /* 125 - r: INT_SUB(riv,r) */
    352, /* 126 - r: INT_SUB(load32,r) */
    353, /* 127 - czr: INT_SUB(riv,load32) */
    354, /* 128 - czr: INT_SUB(load32,riv) */
    360, /* 129 - szpr: INT_USHR(riv,riv) */
    366, /* 130 - szpr: INT_XOR(r,riv) */
    367, /* 131 - szpr: INT_XOR(r,load32) */
    368, /* 132 - szpr: INT_XOR(load32,riv) */
    377, /* 133 - r: LONG_ADD(address1scaledreg,r) */
    378, /* 134 - r: LONG_ADD(r,address1scaledreg) */
    379, /* 135 - r: LONG_ADD(address1scaledreg,address1reg) */
    380, /* 136 - r: LONG_ADD(address1reg,address1scaledreg) */
    383, /* 137 - r: BYTE_LOAD(rlv,rlv) */
    384, /* 138 - sload8: BYTE_LOAD(rlv,rlv) */
    385, /* 139 - r: BYTE_ALOAD(rlv,riv) */
    386, /* 140 - r: BYTE_ALOAD(rlv,r) */
    387, /* 141 - sload8: BYTE_ALOAD(rlv,riv) */
    388, /* 142 - r: UBYTE_LOAD(rlv,rlv) */
    389, /* 143 - uload8: UBYTE_LOAD(rlv,rlv) */
    390, /* 144 - r: UBYTE_ALOAD(rlv,riv) */
    391, /* 145 - r: UBYTE_ALOAD(rlv,r) */
    392, /* 146 - uload8: UBYTE_ALOAD(rlv,riv) */
    395, /* 147 - r: SHORT_LOAD(rlv,rlv) */
    396, /* 148 - sload16: SHORT_LOAD(rlv,rlv) */
    397, /* 149 - r: SHORT_ALOAD(rlv,riv) */
    398, /* 150 - r: SHORT_ALOAD(rlv,r) */
    399, /* 151 - sload16: SHORT_ALOAD(rlv,riv) */
    400, /* 152 - r: USHORT_LOAD(rlv,rlv) */
    401, /* 153 - uload16: USHORT_LOAD(rlv,rlv) */
    402, /* 154 - r: USHORT_ALOAD(rlv,riv) */
    403, /* 155 - r: USHORT_ALOAD(rlv,r) */
    404, /* 156 - uload16: USHORT_ALOAD(rlv,riv) */
    407, /* 157 - load32: INT_LOAD(rlv,rlv) */
    408, /* 158 - load32: INT_ALOAD(rlv,riv) */
    413, /* 159 - load64: LONG_LOAD(rlv,rlv) */
    414, /* 160 - load64: LONG_ALOAD(rlv,rlv) */
    415, /* 161 - load64: LONG_ALOAD(rlv,r) */
    429, /* 162 - czr: LONG_ADD(r,rlv) */
    430, /* 163 - czr: LONG_ADD(r,riv) */
    431, /* 164 - czr: LONG_ADD(r,r) */
    432, /* 165 - r: LONG_ADD(r,rlv) */
    433, /* 166 - czr: LONG_ADD(rlv,load64) */
    434, /* 167 - czr: LONG_ADD(load64,rlv) */
    439, /* 168 - szpr: LONG_AND(r,rlv) */
    440, /* 169 - szpr: LONG_AND(r,r) */
    441, /* 170 - szp: LONG_AND(r,rlv) */
    442, /* 171 - szpr: LONG_AND(rlv,load64) */
    443, /* 172 - szpr: LONG_AND(load64,rlv) */
    444, /* 173 - szp: LONG_AND(load8_16_32_64,rlv) */
    445, /* 174 - szp: LONG_AND(r,load8_16_32_64) */
    450, /* 175 - r: LONG_DIV(rlv,rlv) */
    451, /* 176 - r: LONG_DIV(rlv,riv) */
    452, /* 177 - r: LONG_DIV(riv,rlv) */
    453, /* 178 - r: LONG_DIV(rlv,load64) */
    454, /* 179 - r: LONG_DIV(load64,rlv) */
    455, /* 180 - stm: LONG_IFCMP(rlv,rlv) */
    457, /* 181 - r: LONG_LOAD(rlv,rlv) */
    458, /* 182 - r: LONG_LOAD(rlv,address1scaledreg) */
    459, /* 183 - r: LONG_LOAD(address1scaledreg,rlv) */
    460, /* 184 - r: LONG_LOAD(address1scaledreg,address1reg) */
    461, /* 185 - r: LONG_LOAD(address1reg,address1scaledreg) */
    463, /* 186 - r: LONG_ALOAD(rlv,riv) */
    464, /* 187 - r: LONG_ALOAD(rlv,r) */
    468, /* 188 - r: LONG_MUL(r,rlv) */
    469, /* 189 - r: INT_MUL(r,load64) */
    470, /* 190 - r: INT_MUL(load64,rlv) */
    477, /* 191 - szpr: LONG_OR(r,rlv) */
    478, /* 192 - szpr: LONG_OR(r,load64) */
    479, /* 193 - szpr: LONG_OR(load64,rlv) */
    484, /* 194 - r: LONG_REM(rlv,rlv) */
    485, /* 195 - r: LONG_REM(rlv,riv) */
    486, /* 196 - r: LONG_REM(riv,rlv) */
    487, /* 197 - r: LONG_REM(rlv,load64) */
    488, /* 198 - r: LONG_REM(load64,rlv) */
    490, /* 199 - szpr: LONG_SHL(rlv,riv) */
    499, /* 200 - szpr: LONG_SHR(rlv,riv) */
    511, /* 201 - czr: LONG_SUB(rlv,r) */
    512, /* 202 - r: LONG_SUB(rlv,r) */
    513, /* 203 - r: LONG_SUB(load64,r) */
    514, /* 204 - czr: LONG_SUB(rlv,load64) */
    515, /* 205 - czr: LONG_SUB(load64,rlv) */
    521, /* 206 - szpr: LONG_USHR(rlv,riv) */
    527, /* 207 - szpr: LONG_XOR(r,rlv) */
    528, /* 208 - szpr: LONG_XOR(r,load64) */
    529, /* 209 - szpr: LONG_XOR(load64,rlv) */
    534, /* 210 - r: FLOAT_ADD(r,r) */
    535, /* 211 - r: FLOAT_ADD(r,float_load) */
    536, /* 212 - r: FLOAT_ADD(float_load,r) */
    537, /* 213 - r: DOUBLE_ADD(r,r) */
    538, /* 214 - r: DOUBLE_ADD(r,double_load) */
    539, /* 215 - r: DOUBLE_ADD(double_load,r) */
    540, /* 216 - r: FLOAT_SUB(r,r) */
    541, /* 217 - r: FLOAT_SUB(r,float_load) */
    542, /* 218 - r: DOUBLE_SUB(r,r) */
    543, /* 219 - r: DOUBLE_SUB(r,double_load) */
    544, /* 220 - r: FLOAT_MUL(r,r) */
    545, /* 221 - r: FLOAT_MUL(r,float_load) */
    546, /* 222 - r: FLOAT_MUL(float_load,r) */
    547, /* 223 - r: DOUBLE_MUL(r,r) */
    548, /* 224 - r: DOUBLE_MUL(r,double_load) */
    549, /* 225 - r: DOUBLE_MUL(double_load,r) */
    550, /* 226 - r: FLOAT_DIV(r,r) */
    551, /* 227 - r: FLOAT_DIV(r,float_load) */
    552, /* 228 - r: DOUBLE_DIV(r,r) */
    553, /* 229 - r: DOUBLE_DIV(r,double_load) */
    558, /* 230 - r: FLOAT_REM(r,r) */
    559, /* 231 - r: DOUBLE_REM(r,r) */
    564, /* 232 - r: DOUBLE_LOAD(riv,riv) */
    565, /* 233 - r: DOUBLE_LOAD(riv,rlv) */
    566, /* 234 - r: DOUBLE_LOAD(rlv,rlv) */
    567, /* 235 - double_load: DOUBLE_LOAD(riv,riv) */
    568, /* 236 - r: DOUBLE_ALOAD(riv,riv) */
    569, /* 237 - r: DOUBLE_ALOAD(rlv,riv) */
    570, /* 238 - double_load: DOUBLE_LOAD(rlv,rlv) */
    571, /* 239 - r: DOUBLE_ALOAD(riv,r) */
    572, /* 240 - r: DOUBLE_ALOAD(rlv,rlv) */
    573, /* 241 - double_load: DOUBLE_ALOAD(rlv,riv) */
    574, /* 242 - double_load: DOUBLE_ALOAD(riv,riv) */
    575, /* 243 - r: FLOAT_LOAD(riv,riv) */
    576, /* 244 - r: FLOAT_LOAD(rlv,rlv) */
    577, /* 245 - float_load: FLOAT_LOAD(riv,riv) */
    578, /* 246 - float_load: FLOAT_ALOAD(rlv,riv) */
    579, /* 247 - r: FLOAT_ALOAD(riv,riv) */
    580, /* 248 - r: FLOAT_ALOAD(rlv,riv) */
    581, /* 249 - r: FLOAT_ALOAD(riv,r) */
    582, /* 250 - r: FLOAT_ALOAD(rlv,rlv) */
    583, /* 251 - float_load: FLOAT_ALOAD(riv,riv) */
    626, /* 252 - stm: FLOAT_IFCMP(r,r) */
    627, /* 253 - stm: FLOAT_IFCMP(r,float_load) */
    628, /* 254 - stm: FLOAT_IFCMP(float_load,r) */
    629, /* 255 - stm: DOUBLE_IFCMP(r,r) */
    630, /* 256 - stm: DOUBLE_IFCMP(r,double_load) */
    631, /* 257 - stm: DOUBLE_IFCMP(double_load,r) */
    23, /* 258 - stm: LOWTABLESWITCH(r) */
    28, /* 259 - stm: NULL_CHECK(riv) */
    31, /* 260 - stm: SET_CAUGHT_EXCEPTION(r) */
    35, /* 261 - stm: TRAP_IF(r,INT_CONSTANT) */
    36, /* 262 - stm: TRAP_IF(r,LONG_CONSTANT) */
    40, /* 263 - uload8: INT_AND(load8_16_32,INT_CONSTANT) */
    41, /* 264 - r: INT_AND(load8_16_32,INT_CONSTANT) */
    42, /* 265 - r: INT_2BYTE(load8_16_32) */
    44, /* 266 - r: INT_AND(load16_32,INT_CONSTANT) */
    65, /* 267 - stm: PREFETCH(r) */
    73, /* 268 - stm: RETURN(r) */
    87, /* 269 - address1scaledreg: INT_SHL(r,INT_CONSTANT) */
    88, /* 270 - address1reg: INT_ADD(r,LONG_CONSTANT) */
    89, /* 271 - address1reg: INT_MOVE(r) */
    91, /* 272 - address1reg: INT_ADD(address1reg,LONG_CONSTANT) */
    92, /* 273 - address1scaledreg: INT_ADD(address1scaledreg,LONG_CONSTANT) */
    95, /* 274 - address: INT_ADD(address1scaledreg,LONG_CONSTANT) */
    98, /* 275 - address1scaledreg: LONG_SHL(r,INT_CONSTANT) */
    99, /* 276 - address1reg: LONG_ADD(r,LONG_CONSTANT) */
    100, /* 277 - address1reg: LONG_MOVE(r) */
    102, /* 278 - address1reg: LONG_ADD(address1reg,LONG_CONSTANT) */
    103, /* 279 - address1scaledreg: LONG_ADD(address1scaledreg,LONG_CONSTANT) */
    106, /* 280 - address: LONG_ADD(address1scaledreg,LONG_CONSTANT) */
    165, /* 281 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    166, /* 282 - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    167, /* 283 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    168, /* 284 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) */
    169, /* 285 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) */
    170, /* 286 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) */
    171, /* 287 - r: BOOLEAN_CMP_INT(cz,INT_CONSTANT) */
    172, /* 288 - boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT) */
    173, /* 289 - r: BOOLEAN_CMP_INT(szp,INT_CONSTANT) */
    174, /* 290 - boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT) */
    175, /* 291 - r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) */
    176, /* 292 - boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) */
    177, /* 293 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    178, /* 294 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    179, /* 295 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    180, /* 296 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) */
    189, /* 297 - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) */
    190, /* 298 - boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) */
    191, /* 299 - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) */
    192, /* 300 - r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT) */
    193, /* 301 - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) */
    194, /* 302 - r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT) */
    195, /* 303 - r: BOOLEAN_CMP_LONG(cz,LONG_CONSTANT) */
    200, /* 304 - r: BOOLEAN_NOT(r) */
    209, /* 305 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    210, /* 306 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    211, /* 307 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    212, /* 308 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) */
    224, /* 309 - r: INT_2BYTE(r) */
    225, /* 310 - r: INT_2BYTE(load8_16_32) */
    228, /* 311 - r: INT_2LONG(r) */
    229, /* 312 - r: INT_2LONG(load32) */
    232, /* 313 - r: INT_2ADDRZerExt(r) */
    233, /* 314 - r: INT_2SHORT(r) */
    234, /* 315 - r: INT_2SHORT(load16_32) */
    235, /* 316 - sload16: INT_2SHORT(load16_32) */
    238, /* 317 - szpr: INT_2USHORT(r) */
    239, /* 318 - uload16: INT_2USHORT(load16_32) */
    240, /* 319 - r: INT_2USHORT(load16_32) */
    266, /* 320 - stm: INT_IFCMP(r,INT_CONSTANT) */
    267, /* 321 - stm: INT_IFCMP(load8,INT_CONSTANT) */
    270, /* 322 - stm: INT_IFCMP(sload16,INT_CONSTANT) */
    273, /* 323 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) */
    274, /* 324 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) */
    275, /* 325 - stm: INT_IFCMP(cz,INT_CONSTANT) */
    276, /* 326 - stm: INT_IFCMP(szp,INT_CONSTANT) */
    277, /* 327 - stm: INT_IFCMP(bittest,INT_CONSTANT) */
    286, /* 328 - r: INT_LOAD(address,LONG_CONSTANT) */
    288, /* 329 - r: INT_MOVE(riv) */
    289, /* 330 - czr: INT_MOVE(czr) */
    290, /* 331 - cz: INT_MOVE(cz) */
    291, /* 332 - szpr: INT_MOVE(szpr) */
    292, /* 333 - szp: INT_MOVE(szp) */
    293, /* 334 - sload8: INT_MOVE(sload8) */
    294, /* 335 - uload8: INT_MOVE(uload8) */
    295, /* 336 - load8: INT_MOVE(load8) */
    296, /* 337 - sload16: INT_MOVE(sload16) */
    297, /* 338 - uload16: INT_MOVE(uload16) */
    298, /* 339 - load16: INT_MOVE(load16) */
    299, /* 340 - load32: INT_MOVE(load32) */
    303, /* 341 - szpr: INT_NEG(r) */
    306, /* 342 - r: INT_NOT(r) */
    330, /* 343 - szpr: INT_SHL(r,INT_CONSTANT) */
    331, /* 344 - r: INT_SHL(r,INT_CONSTANT) */
    339, /* 345 - szpr: INT_SHR(riv,INT_CONSTANT) */
    361, /* 346 - szpr: INT_USHR(riv,INT_CONSTANT) */
    381, /* 347 - r: LONG_ADD(address,LONG_CONSTANT) */
    382, /* 348 - r: LONG_MOVE(address) */
    418, /* 349 - r: LONG_2INT(r) */
    421, /* 350 - r: LONG_2INT(load64) */
    422, /* 351 - load32: LONG_2INT(load64) */
    456, /* 352 - stm: LONG_IFCMP(r,LONG_CONSTANT) */
    462, /* 353 - r: LONG_LOAD(address,LONG_CONSTANT) */
    465, /* 354 - r: LONG_MOVE(rlv) */
    466, /* 355 - r: LONG_MOVE(riv) */
    467, /* 356 - load64: LONG_MOVE(load64) */
    471, /* 357 - szpr: LONG_NEG(r) */
    474, /* 358 - r: LONG_NOT(r) */
    491, /* 359 - szpr: LONG_SHL(r,INT_CONSTANT) */
    492, /* 360 - r: LONG_SHL(r,INT_CONSTANT) */
    500, /* 361 - szpr: LONG_SHR(rlv,LONG_CONSTANT) */
    522, /* 362 - szpr: LONG_USHR(rlv,LONG_CONSTANT) */
    554, /* 363 - r: FLOAT_NEG(r) */
    555, /* 364 - r: DOUBLE_NEG(r) */
    556, /* 365 - r: FLOAT_SQRT(r) */
    557, /* 366 - r: DOUBLE_SQRT(r) */
    560, /* 367 - r: LONG_2FLOAT(r) */
    561, /* 368 - r: LONG_2DOUBLE(r) */
    562, /* 369 - r: FLOAT_MOVE(r) */
    563, /* 370 - r: DOUBLE_MOVE(r) */
    602, /* 371 - r: INT_2FLOAT(riv) */
    603, /* 372 - r: INT_2FLOAT(load32) */
    604, /* 373 - r: INT_2DOUBLE(riv) */
    605, /* 374 - r: INT_2DOUBLE(load32) */
    606, /* 375 - r: FLOAT_2DOUBLE(r) */
    607, /* 376 - r: FLOAT_2DOUBLE(float_load) */
    608, /* 377 - r: DOUBLE_2FLOAT(r) */
    609, /* 378 - r: DOUBLE_2FLOAT(double_load) */
    610, /* 379 - r: FLOAT_2INT(r) */
    611, /* 380 - r: FLOAT_2LONG(r) */
    612, /* 381 - r: DOUBLE_2INT(r) */
    613, /* 382 - r: DOUBLE_2LONG(r) */
    614, /* 383 - r: FLOAT_AS_INT_BITS(r) */
    615, /* 384 - load32: FLOAT_AS_INT_BITS(float_load) */
    616, /* 385 - r: DOUBLE_AS_LONG_BITS(r) */
    617, /* 386 - load64: DOUBLE_AS_LONG_BITS(double_load) */
    618, /* 387 - r: INT_BITS_AS_FLOAT(riv) */
    619, /* 388 - float_load: INT_BITS_AS_FLOAT(load32) */
    620, /* 389 - r: LONG_BITS_AS_DOUBLE(rlv) */
    621, /* 390 - double_load: LONG_BITS_AS_DOUBLE(load64) */
    622, /* 391 - r: MATERIALIZE_FP_CONSTANT(any) */
    623, /* 392 - float_load: MATERIALIZE_FP_CONSTANT(any) */
    624, /* 393 - double_load: MATERIALIZE_FP_CONSTANT(any) */
    43, /* 394 - r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT) */
    45, /* 395 - r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT) */
    155, /* 396 - bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT) */
    158, /* 397 - bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) */
    230, /* 398 - r: LONG_AND(INT_2LONG(r),LONG_CONSTANT) */
    231, /* 399 - r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT) */
    332, /* 400 - szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) */
    423, /* 401 - r: LONG_2INT(LONG_USHR(r,INT_CONSTANT)) */
    424, /* 402 - r: LONG_2INT(LONG_SHR(r,INT_CONSTANT)) */
    425, /* 403 - r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) */
    426, /* 404 - r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) */
    427, /* 405 - load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) */
    428, /* 406 - load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) */
    493, /* 407 - szpr: LONG_SHL(LONG_SHR(r,INT_CONSTANT),INT_CONSTANT) */
    46, /* 408 - stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv)) */
    47, /* 409 - stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv)) */
    48, /* 410 - stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv)) */
    49, /* 411 - stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv)) */
    50, /* 412 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv)) */
    51, /* 413 - stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv)) */
    52, /* 414 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r)) */
    53, /* 415 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv)) */
    54, /* 416 - stm: INT_ASTORE(riv,OTHER_OPERAND(r,r)) */
    55, /* 417 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv)) */
    56, /* 418 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv)) */
    57, /* 419 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv)) */
    58, /* 420 - stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv)) */
    59, /* 421 - stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv)) */
    60, /* 422 - stm: LONG_ASTORE(r,OTHER_OPERAND(r,r)) */
    185, /* 423 - stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv)) */
    186, /* 424 - stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv)) */
    203, /* 425 - stm: BYTE_STORE(riv,OTHER_OPERAND(rlv,rlv)) */
    204, /* 426 - stm: BYTE_STORE(load8,OTHER_OPERAND(rlv,rlv)) */
    205, /* 427 - stm: BYTE_ASTORE(riv,OTHER_OPERAND(rlv,riv)) */
    206, /* 428 - stm: BYTE_ASTORE(load8,OTHER_OPERAND(rlv,riv)) */
    207, /* 429 - r: CMP_CMOV(r,OTHER_OPERAND(riv,any)) */
    214, /* 430 - r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any)) */
    215, /* 431 - r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any)) */
    217, /* 432 - r: CMP_CMOV(load32,OTHER_OPERAND(riv,any)) */
    218, /* 433 - r: CMP_CMOV(riv,OTHER_OPERAND(load32,any)) */
    344, /* 434 - stm: INT_STORE(riv,OTHER_OPERAND(rlv,rlv)) */
    345, /* 435 - stm: INT_STORE(riv,OTHER_OPERAND(rlv,address1scaledreg)) */
    346, /* 436 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,rlv)) */
    347, /* 437 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg)) */
    348, /* 438 - stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg)) */
    373, /* 439 - r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any)) */
    375, /* 440 - r: LCMP_CMOV(load64,OTHER_OPERAND(rlv,any)) */
    376, /* 441 - r: LCMP_CMOV(rlv,OTHER_OPERAND(load64,any)) */
    505, /* 442 - stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,rlv)) */
    506, /* 443 - stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,address1scaledreg)) */
    507, /* 444 - stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,rlv)) */
    508, /* 445 - stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,address1reg)) */
    509, /* 446 - stm: LONG_STORE(rlv,OTHER_OPERAND(address1reg,address1scaledreg)) */
    584, /* 447 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv)) */
    585, /* 448 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv)) */
    586, /* 449 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv)) */
    587, /* 450 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv)) */
    588, /* 451 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv)) */
    589, /* 452 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv)) */
    590, /* 453 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv)) */
    591, /* 454 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv)) */
    592, /* 455 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r)) */
    593, /* 456 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv)) */
    594, /* 457 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv)) */
    595, /* 458 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv)) */
    596, /* 459 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv)) */
    597, /* 460 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv)) */
    598, /* 461 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv)) */
    599, /* 462 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv)) */
    600, /* 463 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv)) */
    601, /* 464 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r)) */
    632, /* 465 - r: FCMP_CMOV(r,OTHER_OPERAND(r,any)) */
    633, /* 466 - r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any)) */
    634, /* 467 - r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any)) */
    635, /* 468 - r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any)) */
    636, /* 469 - r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any)) */
    637, /* 470 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,any)) */
    642, /* 471 - r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any)) */
    643, /* 472 - r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any)) */
    660, /* 473 - stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv)) */
    661, /* 474 - stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv)) */
    662, /* 475 - stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv)) */
    663, /* 476 - stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv)) */
    61, /* 477 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv)) */
    62, /* 478 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv)) */
    76, /* 479 - r: CALL(BRANCH_TARGET,any) */
    78, /* 480 - r: CALL(INT_CONSTANT,any) */
    82, /* 481 - r: SYSCALL(INT_CONSTANT,any) */
    77, /* 482 - r: CALL(INT_LOAD(riv,riv),any) */
    79, /* 483 - r: CALL(LONG_LOAD(rlv,rlv),any) */
    81, /* 484 - r: SYSCALL(INT_LOAD(riv,riv),any) */
    109, /* 485 - r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))) */
    110, /* 486 - r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) */
    111, /* 487 - r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) */
    112, /* 488 - r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) */
    113, /* 489 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))) */
    114, /* 490 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))) */
    115, /* 491 - r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) */
    132, /* 492 - r: ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))) */
    133, /* 493 - r: ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))) */
    134, /* 494 - r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))) */
    135, /* 495 - r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))) */
    136, /* 496 - r: ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))) */
    638, /* 497 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load))) */
    639, /* 498 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load))) */
    640, /* 499 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r))) */
    641, /* 500 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r))) */
    116, /* 501 - r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))) */
    137, /* 502 - r: ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))) */
    117, /* 503 - r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))) */
    138, /* 504 - r: ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))) */
    118, /* 505 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    119, /* 506 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    120, /* 507 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    121, /* 508 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    122, /* 509 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    125, /* 510 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    126, /* 511 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    127, /* 512 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    128, /* 513 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    129, /* 514 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    139, /* 515 - stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    140, /* 516 - stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    141, /* 517 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    142, /* 518 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    143, /* 519 - stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    146, /* 520 - stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    147, /* 521 - stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    148, /* 522 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    149, /* 523 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    150, /* 524 - stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    123, /* 525 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    130, /* 526 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    144, /* 527 - stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    151, /* 528 - stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    124, /* 529 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    131, /* 530 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) */
    145, /* 531 - stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    152, /* 532 - stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) */
    153, /* 533 - bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    154, /* 534 - bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    156, /* 535 - bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    157, /* 536 - bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) */
    159, /* 537 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r) */
    160, /* 538 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32) */
    161, /* 539 - bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) */
    162, /* 540 - bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) */
    201, /* 541 - stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    202, /* 542 - stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv,riv)) */
    304, /* 543 - stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    305, /* 544 - stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    307, /* 545 - stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    308, /* 546 - stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    334, /* 547 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    336, /* 548 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    341, /* 549 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    343, /* 550 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    363, /* 551 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    365, /* 552 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    472, /* 553 - stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    473, /* 554 - stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    475, /* 555 - stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    476, /* 556 - stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    495, /* 557 - stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    497, /* 558 - stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) */
    502, /* 559 - stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) */
    504, /* 560 - stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) */
    524, /* 561 - stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) */
    526, /* 562 - stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) */
    208, /* 563 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any)) */
    213, /* 564 - r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any)) */
    216, /* 565 - r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any)) */
    219, /* 566 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) */
    220, /* 567 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) */
    221, /* 568 - r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any)) */
    222, /* 569 - r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any)) */
    223, /* 570 - r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any)) */
    374, /* 571 - r: LCMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any)) */
    226, /* 572 - stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) */
    227, /* 573 - stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) */
    236, /* 574 - stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) */
    237, /* 575 - stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) */
    241, /* 576 - stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) */
    242, /* 577 - stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) */
    419, /* 578 - stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) */
    420, /* 579 - stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) */
    247, /* 580 - stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    249, /* 581 - stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    257, /* 582 - stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    259, /* 583 - stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    312, /* 584 - stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    314, /* 585 - stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    355, /* 586 - stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    357, /* 587 - stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    369, /* 588 - stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    371, /* 589 - stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) */
    435, /* 590 - stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    437, /* 591 - stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    446, /* 592 - stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    448, /* 593 - stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    480, /* 594 - stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    482, /* 595 - stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    516, /* 596 - stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    518, /* 597 - stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    530, /* 598 - stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    532, /* 599 - stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) */
    248, /* 600 - stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    250, /* 601 - stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    258, /* 602 - stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    260, /* 603 - stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    313, /* 604 - stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    315, /* 605 - stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    356, /* 606 - stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    358, /* 607 - stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    370, /* 608 - stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    372, /* 609 - stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) */
    436, /* 610 - stm: LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    438, /* 611 - stm: LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    447, /* 612 - stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    449, /* 613 - stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    481, /* 614 - stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    483, /* 615 - stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    517, /* 616 - stm: LONG_STORE(LONG_SUB(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    519, /* 617 - stm: LONG_ASTORE(LONG_SUB(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    531, /* 618 - stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    533, /* 619 - stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) */
    320, /* 620 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) */
    321, /* 621 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) */
    322, /* 622 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) */
    323, /* 623 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) */
    324, /* 624 - r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT))) */
    327, /* 625 - r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT))) */
    325, /* 626 - r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT))) */
    326, /* 627 - r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT))) */
    328, /* 628 - szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT)) */
    337, /* 629 - szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT)) */
    349, /* 630 - stm: INT_STORE(riv,OTHER_OPERAND(address,LONG_CONSTANT)) */
    359, /* 631 - szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT)) */
    489, /* 632 - szpr: LONG_SHL(rlv,INT_AND(r,INT_CONSTANT)) */
    498, /* 633 - szpr: LONG_SHR(rlv,INT_AND(r,LONG_CONSTANT)) */
    510, /* 634 - stm: LONG_STORE(rlv,OTHER_OPERAND(address,LONG_CONSTANT)) */
    520, /* 635 - szpr: LONG_USHR(rlv,LONG_AND(r,LONG_CONSTANT)) */
    333, /* 636 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    335, /* 637 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    340, /* 638 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    342, /* 639 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    362, /* 640 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    364, /* 641 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    494, /* 642 - stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    496, /* 643 - stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    501, /* 644 - stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    503, /* 645 - stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    523, /* 646 - stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    525, /* 647 - stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) */
    644, /* 648 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    645, /* 649 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    652, /* 650 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) */
    653, /* 651 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) */
    646, /* 652 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) */
    647, /* 653 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) */
    654, /* 654 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    655, /* 655 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    648, /* 656 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) */
    649, /* 657 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) */
    656, /* 658 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    657, /* 659 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) */
    650, /* 660 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    651, /* 661 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) */
    658, /* 662 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r)))) */
  };

  /** Ragged array for non-terminal leaves of r_NT,  */
  private static final byte[] nts_0 = { r_NT,  };
  /** Ragged array for non-terminal leaves of czr_NT,  */
  private static final byte[] nts_1 = { czr_NT,  };
  /** Ragged array for non-terminal leaves of szpr_NT,  */
  private static final byte[] nts_2 = { szpr_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT,  */
  private static final byte[] nts_3 = { riv_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT,  */
  private static final byte[] nts_4 = { address1reg_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT,  */
  private static final byte[] nts_5 = { address1scaledreg_NT,  };
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
  /** Ragged array for non-terminal leaves of load64_NT,  */
  private static final byte[] nts_14 = { load64_NT,  };
  /** Ragged array for non-terminal leaves of load8_16_32_NT,  */
  private static final byte[] nts_15 = { load8_16_32_NT,  };
  /** Ragged array for non-terminal leaves of  */
  private static final byte[] nts_16 = {  };
  /** Ragged array for non-terminal leaves of any_NT, any_NT,  */
  private static final byte[] nts_17 = { any_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT,  */
  private static final byte[] nts_18 = { r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT, riv_NT,  */
  private static final byte[] nts_19 = { load32_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, load32_NT,  */
  private static final byte[] nts_20 = { riv_NT, load32_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT,  */
  private static final byte[] nts_21 = { rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, any_NT,  */
  private static final byte[] nts_22 = { r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, address1scaledreg_NT,  */
  private static final byte[] nts_23 = { r_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, r_NT,  */
  private static final byte[] nts_24 = { address1scaledreg_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, address1reg_NT,  */
  private static final byte[] nts_25 = { address1scaledreg_NT, address1reg_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT, address1scaledreg_NT,  */
  private static final byte[] nts_26 = { address1reg_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT,  */
  private static final byte[] nts_27 = { r_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load32_NT,  */
  private static final byte[] nts_28 = { r_NT, load32_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT,  */
  private static final byte[] nts_29 = { r_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, rlv_NT,  */
  private static final byte[] nts_30 = { load64_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load64_NT,  */
  private static final byte[] nts_31 = { r_NT, load64_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, load64_NT,  */
  private static final byte[] nts_32 = { rlv_NT, load64_NT,  };
  /** Ragged array for non-terminal leaves of load8_16_32_NT, riv_NT,  */
  private static final byte[] nts_33 = { load8_16_32_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load8_16_32_NT,  */
  private static final byte[] nts_34 = { r_NT, load8_16_32_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT,  */
  private static final byte[] nts_35 = { riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, riv_NT,  */
  private static final byte[] nts_36 = { rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, load32_NT,  */
  private static final byte[] nts_37 = { rlv_NT, load32_NT,  };
  /** Ragged array for non-terminal leaves of uload8_NT, r_NT,  */
  private static final byte[] nts_38 = { uload8_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, uload8_NT,  */
  private static final byte[] nts_39 = { r_NT, uload8_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, address1scaledreg_NT,  */
  private static final byte[] nts_40 = { rlv_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, rlv_NT,  */
  private static final byte[] nts_41 = { address1scaledreg_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, r_NT,  */
  private static final byte[] nts_42 = { riv_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT, r_NT,  */
  private static final byte[] nts_43 = { load32_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, r_NT,  */
  private static final byte[] nts_44 = { rlv_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of load8_16_32_64_NT, rlv_NT,  */
  private static final byte[] nts_45 = { load8_16_32_64_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, load8_16_32_64_NT,  */
  private static final byte[] nts_46 = { r_NT, load8_16_32_64_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT,  */
  private static final byte[] nts_47 = { riv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, r_NT,  */
  private static final byte[] nts_48 = { load64_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, float_load_NT,  */
  private static final byte[] nts_49 = { r_NT, float_load_NT,  };
  /** Ragged array for non-terminal leaves of float_load_NT, r_NT,  */
  private static final byte[] nts_50 = { float_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, double_load_NT,  */
  private static final byte[] nts_51 = { r_NT, double_load_NT,  };
  /** Ragged array for non-terminal leaves of double_load_NT, r_NT,  */
  private static final byte[] nts_52 = { double_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of cz_NT,  */
  private static final byte[] nts_53 = { cz_NT,  };
  /** Ragged array for non-terminal leaves of szp_NT,  */
  private static final byte[] nts_54 = { szp_NT,  };
  /** Ragged array for non-terminal leaves of bittest_NT,  */
  private static final byte[] nts_55 = { bittest_NT,  };
  /** Ragged array for non-terminal leaves of boolcmp_NT,  */
  private static final byte[] nts_56 = { boolcmp_NT,  };
  /** Ragged array for non-terminal leaves of address_NT,  */
  private static final byte[] nts_57 = { address_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT,  */
  private static final byte[] nts_58 = { rlv_NT,  };
  /** Ragged array for non-terminal leaves of float_load_NT,  */
  private static final byte[] nts_59 = { float_load_NT,  };
  /** Ragged array for non-terminal leaves of double_load_NT,  */
  private static final byte[] nts_60 = { double_load_NT,  };
  /** Ragged array for non-terminal leaves of any_NT,  */
  private static final byte[] nts_61 = { any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_62 = { riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load16_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_63 = { load16_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_64 = { rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_65 = { riv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, r_NT, r_NT,  */
  private static final byte[] nts_66 = { riv_NT, r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_67 = { riv_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, rlv_NT,  */
  private static final byte[] nts_68 = { riv_NT, riv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_69 = { r_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_70 = { r_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT,  */
  private static final byte[] nts_71 = { r_NT, r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of boolcmp_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_72 = { boolcmp_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load8_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_73 = { load8_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of load8_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_74 = { load8_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, any_NT,  */
  private static final byte[] nts_75 = { r_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of uload8_NT, riv_NT, any_NT,  */
  private static final byte[] nts_76 = { uload8_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, uload8_NT, any_NT,  */
  private static final byte[] nts_77 = { riv_NT, uload8_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of load32_NT, riv_NT, any_NT,  */
  private static final byte[] nts_78 = { load32_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, load32_NT, any_NT,  */
  private static final byte[] nts_79 = { riv_NT, load32_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, address1scaledreg_NT,  */
  private static final byte[] nts_80 = { riv_NT, rlv_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1scaledreg_NT, rlv_NT,  */
  private static final byte[] nts_81 = { riv_NT, address1scaledreg_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1scaledreg_NT, address1reg_NT,  */
  private static final byte[] nts_82 = { riv_NT, address1scaledreg_NT, address1reg_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address1reg_NT, address1scaledreg_NT,  */
  private static final byte[] nts_83 = { riv_NT, address1reg_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, any_NT,  */
  private static final byte[] nts_84 = { r_NT, rlv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, rlv_NT, any_NT,  */
  private static final byte[] nts_85 = { load64_NT, rlv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, load64_NT, any_NT,  */
  private static final byte[] nts_86 = { rlv_NT, load64_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, address1scaledreg_NT,  */
  private static final byte[] nts_87 = { rlv_NT, rlv_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, address1scaledreg_NT, rlv_NT,  */
  private static final byte[] nts_88 = { rlv_NT, address1scaledreg_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, address1scaledreg_NT, address1reg_NT,  */
  private static final byte[] nts_89 = { rlv_NT, address1scaledreg_NT, address1reg_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, address1reg_NT, address1scaledreg_NT,  */
  private static final byte[] nts_90 = { rlv_NT, address1reg_NT, address1scaledreg_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, rlv_NT,  */
  private static final byte[] nts_91 = { r_NT, riv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_92 = { r_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, any_NT,  */
  private static final byte[] nts_93 = { r_NT, r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, float_load_NT, any_NT,  */
  private static final byte[] nts_94 = { r_NT, float_load_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, double_load_NT, any_NT,  */
  private static final byte[] nts_95 = { r_NT, double_load_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of float_load_NT, r_NT, any_NT,  */
  private static final byte[] nts_96 = { float_load_NT, r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of double_load_NT, r_NT, any_NT,  */
  private static final byte[] nts_97 = { double_load_NT, r_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_98 = { load64_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load64_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_99 = { load64_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, any_NT,  */
  private static final byte[] nts_100 = { riv_NT, riv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, any_NT,  */
  private static final byte[] nts_101 = { rlv_NT, rlv_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_102 = { riv_NT, riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, rlv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_103 = { riv_NT, rlv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_104 = { rlv_NT, rlv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, address1scaledreg_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_105 = { r_NT, address1scaledreg_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, r_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_106 = { address1scaledreg_NT, r_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, address1reg_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_107 = { address1scaledreg_NT, address1reg_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT, address1scaledreg_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_108 = { address1reg_NT, address1scaledreg_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_109 = { rlv_NT, rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, address1scaledreg_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_110 = { r_NT, address1scaledreg_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, r_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_111 = { address1scaledreg_NT, r_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of address1scaledreg_NT, address1reg_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_112 = { address1scaledreg_NT, address1reg_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of address1reg_NT, address1scaledreg_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_113 = { address1reg_NT, address1scaledreg_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT, float_load_NT,  */
  private static final byte[] nts_114 = { r_NT, r_NT, r_NT, float_load_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT, double_load_NT,  */
  private static final byte[] nts_115 = { r_NT, r_NT, r_NT, double_load_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, float_load_NT, r_NT,  */
  private static final byte[] nts_116 = { r_NT, r_NT, float_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, double_load_NT, r_NT,  */
  private static final byte[] nts_117 = { r_NT, r_NT, double_load_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of address_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_118 = { address_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of address_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_119 = { address_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, riv_NT, rlv_NT, riv_NT,  */
  private static final byte[] nts_120 = { rlv_NT, riv_NT, rlv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of load8_NT, any_NT,  */
  private static final byte[] nts_121 = { load8_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of sload16_NT, any_NT,  */
  private static final byte[] nts_122 = { sload16_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of boolcmp_NT, any_NT,  */
  private static final byte[] nts_123 = { boolcmp_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of bittest_NT, any_NT,  */
  private static final byte[] nts_124 = { bittest_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of cz_NT, any_NT,  */
  private static final byte[] nts_125 = { cz_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of szp_NT, any_NT,  */
  private static final byte[] nts_126 = { szp_NT, any_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_127 = { riv_NT, riv_NT, riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_128 = { rlv_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, riv_NT, riv_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_129 = { r_NT, riv_NT, riv_NT, riv_NT, riv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  */
  private static final byte[] nts_130 = { r_NT, rlv_NT, rlv_NT, rlv_NT, rlv_NT,  };
  /** Ragged array for non-terminal leaves of r_NT, r_NT, r_NT, r_NT,  */
  private static final byte[] nts_131 = { r_NT, r_NT, r_NT, r_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, address_NT,  */
  private static final byte[] nts_132 = { riv_NT, address_NT,  };
  /** Ragged array for non-terminal leaves of rlv_NT, address_NT,  */
  private static final byte[] nts_133 = { rlv_NT, address_NT,  };
  /** Ragged array for non-terminal leaves of riv_NT, riv_NT, r_NT, riv_NT, riv_NT,  */
  private static final byte[] nts_134 = { riv_NT, riv_NT, r_NT, riv_NT, riv_NT,  };

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
    nts_4,  // 9 - address1scaledreg: address1reg 
    nts_5,  // 10 - address: address1scaledreg 
    nts_6,  // 11 - load8: sload8 
    nts_7,  // 12 - load8: uload8 
    nts_8,  // 13 - load16: sload16 
    nts_9,  // 14 - load16: uload16 
    nts_10, // 15 - load16_32: load16 
    nts_11, // 16 - load16_32: load32 
    nts_12, // 17 - load8_16_32: load16_32 
    nts_13, // 18 - load8_16_32: load8 
    nts_14, // 19 - load8_16_32_64: load64 
    nts_15, // 20 - load8_16_32_64: load8_16_32 
    nts_16, // 21 - r: REGISTER 
    nts_16, // 22 - riv: INT_CONSTANT 
    nts_16, // 23 - rlv: LONG_CONSTANT 
    nts_16, // 24 - any: NULL 
    nts_16, // 25 - any: ADDRESS_CONSTANT 
    nts_16, // 26 - any: LONG_CONSTANT 
    nts_16, // 27 - stm: IG_PATCH_POINT 
    nts_16, // 28 - stm: UNINT_BEGIN 
    nts_16, // 29 - stm: UNINT_END 
    nts_16, // 30 - stm: YIELDPOINT_PROLOGUE 
    nts_16, // 31 - stm: YIELDPOINT_EPILOGUE 
    nts_16, // 32 - stm: YIELDPOINT_BACKEDGE 
    nts_16, // 33 - r: FRAMESIZE 
    nts_16, // 34 - stm: RESOLVE 
    nts_16, // 35 - stm: NOP 
    nts_16, // 36 - r: GUARD_MOVE 
    nts_16, // 37 - r: GUARD_COMBINE 
    nts_16, // 38 - stm: IR_PROLOGUE 
    nts_16, // 39 - r: GET_CAUGHT_EXCEPTION 
    nts_16, // 40 - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT) 
    nts_16, // 41 - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT) 
    nts_16, // 42 - stm: TRAP 
    nts_16, // 43 - stm: GOTO 
    nts_16, // 44 - stm: WRITE_FLOOR 
    nts_16, // 45 - stm: READ_CEILING 
    nts_16, // 46 - stm: FENCE 
    nts_16, // 47 - stm: PAUSE 
    nts_16, // 48 - stm: ILLEGAL_INSTRUCTION 
    nts_16, // 49 - stm: RETURN(NULL) 
    nts_16, // 50 - stm: RETURN(INT_CONSTANT) 
    nts_16, // 51 - stm: RETURN(LONG_CONSTANT) 
    nts_16, // 52 - r: GET_TIME_BASE 
    nts_16, // 53 - stm: CLEAR_FLOATING_POINT_STATE 
    nts_17, // 54 - any: OTHER_OPERAND(any,any) 
    nts_18, // 55 - stm: TRAP_IF(r,r) 
    nts_19, // 56 - stm: TRAP_IF(load32,riv) 
    nts_20, // 57 - stm: TRAP_IF(riv,load32) 
    nts_21, // 58 - r: LONG_CMP(rlv,rlv) 
    nts_22, // 59 - r: CALL(r,any) 
    nts_22, // 60 - r: SYSCALL(r,any) 
    nts_17, // 61 - stm: YIELDPOINT_OSR(any,any) 
    nts_18, // 62 - address: INT_ADD(r,r) 
    nts_23, // 63 - address: INT_ADD(r,address1scaledreg) 
    nts_24, // 64 - address: INT_ADD(address1scaledreg,r) 
    nts_25, // 65 - address: INT_ADD(address1scaledreg,address1reg) 
    nts_26, // 66 - address: INT_ADD(address1reg,address1scaledreg) 
    nts_18, // 67 - address: LONG_ADD(r,r) 
    nts_23, // 68 - address: LONG_ADD(r,address1scaledreg) 
    nts_24, // 69 - address: LONG_ADD(address1scaledreg,r) 
    nts_25, // 70 - address: LONG_ADD(address1scaledreg,address1reg) 
    nts_26, // 71 - address: LONG_ADD(address1reg,address1scaledreg) 
    nts_27, // 72 - r: BOOLEAN_CMP_INT(r,riv) 
    nts_27, // 73 - boolcmp: BOOLEAN_CMP_INT(r,riv) 
    nts_19, // 74 - r: BOOLEAN_CMP_INT(load32,riv) 
    nts_19, // 75 - boolcmp: BOOLEAN_CMP_INT(load32,riv) 
    nts_28, // 76 - r: BOOLEAN_CMP_INT(r,load32) 
    nts_20, // 77 - boolcmp: BOOLEAN_CMP_INT(riv,load32) 
    nts_29, // 78 - r: BOOLEAN_CMP_LONG(r,rlv) 
    nts_29, // 79 - boolcmp: BOOLEAN_CMP_LONG(r,rlv) 
    nts_30, // 80 - r: BOOLEAN_CMP_LONG(load64,rlv) 
    nts_30, // 81 - boolcmp: BOOLEAN_CMP_LONG(load64,rlv) 
    nts_31, // 82 - r: BOOLEAN_CMP_LONG(r,load64) 
    nts_32, // 83 - boolcmp: BOOLEAN_CMP_LONG(rlv,load64) 
    nts_27, // 84 - czr: INT_ADD(r,riv) 
    nts_27, // 85 - r: INT_ADD(r,riv) 
    nts_28, // 86 - czr: INT_ADD(r,load32) 
    nts_19, // 87 - czr: INT_ADD(load32,riv) 
    nts_27, // 88 - szpr: INT_AND(r,riv) 
    nts_27, // 89 - szp: INT_AND(r,riv) 
    nts_28, // 90 - szpr: INT_AND(r,load32) 
    nts_19, // 91 - szpr: INT_AND(load32,riv) 
    nts_33, // 92 - szp: INT_AND(load8_16_32,riv) 
    nts_34, // 93 - szp: INT_AND(r,load8_16_32) 
    nts_35, // 94 - r: INT_DIV(riv,riv) 
    nts_20, // 95 - r: INT_DIV(riv,load32) 
    nts_36, // 96 - r: UNSIGNED_DIV_64_32(rlv,riv) 
    nts_37, // 97 - r: UNSIGNED_DIV_64_32(rlv,load32) 
    nts_27, // 98 - stm: INT_IFCMP(r,riv) 
    nts_38, // 99 - stm: INT_IFCMP(uload8,r) 
    nts_39, // 100 - stm: INT_IFCMP(r,uload8) 
    nts_19, // 101 - stm: INT_IFCMP(load32,riv) 
    nts_28, // 102 - stm: INT_IFCMP(r,load32) 
    nts_27, // 103 - stm: INT_IFCMP2(r,riv) 
    nts_19, // 104 - stm: INT_IFCMP2(load32,riv) 
    nts_20, // 105 - stm: INT_IFCMP2(riv,load32) 
    nts_21, // 106 - r: INT_LOAD(rlv,rlv) 
    nts_40, // 107 - r: INT_LOAD(rlv,address1scaledreg) 
    nts_41, // 108 - r: INT_LOAD(address1scaledreg,rlv) 
    nts_25, // 109 - r: INT_LOAD(address1scaledreg,address1reg) 
    nts_26, // 110 - r: INT_LOAD(address1reg,address1scaledreg) 
    nts_36, // 111 - r: INT_ALOAD(rlv,riv) 
    nts_27, // 112 - r: INT_MUL(r,riv) 
    nts_28, // 113 - r: INT_MUL(r,load32) 
    nts_19, // 114 - r: INT_MUL(load32,riv) 
    nts_27, // 115 - szpr: INT_OR(r,riv) 
    nts_28, // 116 - szpr: INT_OR(r,load32) 
    nts_19, // 117 - szpr: INT_OR(load32,riv) 
    nts_35, // 118 - r: INT_REM(riv,riv) 
    nts_20, // 119 - r: INT_REM(riv,load32) 
    nts_36, // 120 - r: UNSIGNED_REM_64_32(rlv,riv) 
    nts_37, // 121 - r: UNSIGNED_REM_64_32(rlv,load32) 
    nts_35, // 122 - szpr: INT_SHL(riv,riv) 
    nts_35, // 123 - szpr: INT_SHR(riv,riv) 
    nts_42, // 124 - czr: INT_SUB(riv,r) 
    nts_42, // 125 - r: INT_SUB(riv,r) 
    nts_43, // 126 - r: INT_SUB(load32,r) 
    nts_20, // 127 - czr: INT_SUB(riv,load32) 
    nts_19, // 128 - czr: INT_SUB(load32,riv) 
    nts_35, // 129 - szpr: INT_USHR(riv,riv) 
    nts_27, // 130 - szpr: INT_XOR(r,riv) 
    nts_28, // 131 - szpr: INT_XOR(r,load32) 
    nts_19, // 132 - szpr: INT_XOR(load32,riv) 
    nts_24, // 133 - r: LONG_ADD(address1scaledreg,r) 
    nts_23, // 134 - r: LONG_ADD(r,address1scaledreg) 
    nts_25, // 135 - r: LONG_ADD(address1scaledreg,address1reg) 
    nts_26, // 136 - r: LONG_ADD(address1reg,address1scaledreg) 
    nts_21, // 137 - r: BYTE_LOAD(rlv,rlv) 
    nts_21, // 138 - sload8: BYTE_LOAD(rlv,rlv) 
    nts_36, // 139 - r: BYTE_ALOAD(rlv,riv) 
    nts_44, // 140 - r: BYTE_ALOAD(rlv,r) 
    nts_36, // 141 - sload8: BYTE_ALOAD(rlv,riv) 
    nts_21, // 142 - r: UBYTE_LOAD(rlv,rlv) 
    nts_21, // 143 - uload8: UBYTE_LOAD(rlv,rlv) 
    nts_36, // 144 - r: UBYTE_ALOAD(rlv,riv) 
    nts_44, // 145 - r: UBYTE_ALOAD(rlv,r) 
    nts_36, // 146 - uload8: UBYTE_ALOAD(rlv,riv) 
    nts_21, // 147 - r: SHORT_LOAD(rlv,rlv) 
    nts_21, // 148 - sload16: SHORT_LOAD(rlv,rlv) 
    nts_36, // 149 - r: SHORT_ALOAD(rlv,riv) 
    nts_44, // 150 - r: SHORT_ALOAD(rlv,r) 
    nts_36, // 151 - sload16: SHORT_ALOAD(rlv,riv) 
    nts_21, // 152 - r: USHORT_LOAD(rlv,rlv) 
    nts_21, // 153 - uload16: USHORT_LOAD(rlv,rlv) 
    nts_36, // 154 - r: USHORT_ALOAD(rlv,riv) 
    nts_44, // 155 - r: USHORT_ALOAD(rlv,r) 
    nts_36, // 156 - uload16: USHORT_ALOAD(rlv,riv) 
    nts_21, // 157 - load32: INT_LOAD(rlv,rlv) 
    nts_36, // 158 - load32: INT_ALOAD(rlv,riv) 
    nts_21, // 159 - load64: LONG_LOAD(rlv,rlv) 
    nts_21, // 160 - load64: LONG_ALOAD(rlv,rlv) 
    nts_44, // 161 - load64: LONG_ALOAD(rlv,r) 
    nts_29, // 162 - czr: LONG_ADD(r,rlv) 
    nts_27, // 163 - czr: LONG_ADD(r,riv) 
    nts_18, // 164 - czr: LONG_ADD(r,r) 
    nts_29, // 165 - r: LONG_ADD(r,rlv) 
    nts_32, // 166 - czr: LONG_ADD(rlv,load64) 
    nts_30, // 167 - czr: LONG_ADD(load64,rlv) 
    nts_29, // 168 - szpr: LONG_AND(r,rlv) 
    nts_18, // 169 - szpr: LONG_AND(r,r) 
    nts_29, // 170 - szp: LONG_AND(r,rlv) 
    nts_32, // 171 - szpr: LONG_AND(rlv,load64) 
    nts_30, // 172 - szpr: LONG_AND(load64,rlv) 
    nts_45, // 173 - szp: LONG_AND(load8_16_32_64,rlv) 
    nts_46, // 174 - szp: LONG_AND(r,load8_16_32_64) 
    nts_21, // 175 - r: LONG_DIV(rlv,rlv) 
    nts_36, // 176 - r: LONG_DIV(rlv,riv) 
    nts_47, // 177 - r: LONG_DIV(riv,rlv) 
    nts_32, // 178 - r: LONG_DIV(rlv,load64) 
    nts_30, // 179 - r: LONG_DIV(load64,rlv) 
    nts_21, // 180 - stm: LONG_IFCMP(rlv,rlv) 
    nts_21, // 181 - r: LONG_LOAD(rlv,rlv) 
    nts_40, // 182 - r: LONG_LOAD(rlv,address1scaledreg) 
    nts_41, // 183 - r: LONG_LOAD(address1scaledreg,rlv) 
    nts_25, // 184 - r: LONG_LOAD(address1scaledreg,address1reg) 
    nts_26, // 185 - r: LONG_LOAD(address1reg,address1scaledreg) 
    nts_36, // 186 - r: LONG_ALOAD(rlv,riv) 
    nts_44, // 187 - r: LONG_ALOAD(rlv,r) 
    nts_29, // 188 - r: LONG_MUL(r,rlv) 
    nts_31, // 189 - r: INT_MUL(r,load64) 
    nts_30, // 190 - r: INT_MUL(load64,rlv) 
    nts_29, // 191 - szpr: LONG_OR(r,rlv) 
    nts_31, // 192 - szpr: LONG_OR(r,load64) 
    nts_30, // 193 - szpr: LONG_OR(load64,rlv) 
    nts_21, // 194 - r: LONG_REM(rlv,rlv) 
    nts_36, // 195 - r: LONG_REM(rlv,riv) 
    nts_47, // 196 - r: LONG_REM(riv,rlv) 
    nts_32, // 197 - r: LONG_REM(rlv,load64) 
    nts_30, // 198 - r: LONG_REM(load64,rlv) 
    nts_36, // 199 - szpr: LONG_SHL(rlv,riv) 
    nts_36, // 200 - szpr: LONG_SHR(rlv,riv) 
    nts_44, // 201 - czr: LONG_SUB(rlv,r) 
    nts_44, // 202 - r: LONG_SUB(rlv,r) 
    nts_48, // 203 - r: LONG_SUB(load64,r) 
    nts_32, // 204 - czr: LONG_SUB(rlv,load64) 
    nts_30, // 205 - czr: LONG_SUB(load64,rlv) 
    nts_36, // 206 - szpr: LONG_USHR(rlv,riv) 
    nts_29, // 207 - szpr: LONG_XOR(r,rlv) 
    nts_31, // 208 - szpr: LONG_XOR(r,load64) 
    nts_30, // 209 - szpr: LONG_XOR(load64,rlv) 
    nts_18, // 210 - r: FLOAT_ADD(r,r) 
    nts_49, // 211 - r: FLOAT_ADD(r,float_load) 
    nts_50, // 212 - r: FLOAT_ADD(float_load,r) 
    nts_18, // 213 - r: DOUBLE_ADD(r,r) 
    nts_51, // 214 - r: DOUBLE_ADD(r,double_load) 
    nts_52, // 215 - r: DOUBLE_ADD(double_load,r) 
    nts_18, // 216 - r: FLOAT_SUB(r,r) 
    nts_49, // 217 - r: FLOAT_SUB(r,float_load) 
    nts_18, // 218 - r: DOUBLE_SUB(r,r) 
    nts_51, // 219 - r: DOUBLE_SUB(r,double_load) 
    nts_18, // 220 - r: FLOAT_MUL(r,r) 
    nts_49, // 221 - r: FLOAT_MUL(r,float_load) 
    nts_50, // 222 - r: FLOAT_MUL(float_load,r) 
    nts_18, // 223 - r: DOUBLE_MUL(r,r) 
    nts_51, // 224 - r: DOUBLE_MUL(r,double_load) 
    nts_52, // 225 - r: DOUBLE_MUL(double_load,r) 
    nts_18, // 226 - r: FLOAT_DIV(r,r) 
    nts_49, // 227 - r: FLOAT_DIV(r,float_load) 
    nts_18, // 228 - r: DOUBLE_DIV(r,r) 
    nts_51, // 229 - r: DOUBLE_DIV(r,double_load) 
    nts_18, // 230 - r: FLOAT_REM(r,r) 
    nts_18, // 231 - r: DOUBLE_REM(r,r) 
    nts_35, // 232 - r: DOUBLE_LOAD(riv,riv) 
    nts_47, // 233 - r: DOUBLE_LOAD(riv,rlv) 
    nts_21, // 234 - r: DOUBLE_LOAD(rlv,rlv) 
    nts_35, // 235 - double_load: DOUBLE_LOAD(riv,riv) 
    nts_35, // 236 - r: DOUBLE_ALOAD(riv,riv) 
    nts_36, // 237 - r: DOUBLE_ALOAD(rlv,riv) 
    nts_21, // 238 - double_load: DOUBLE_LOAD(rlv,rlv) 
    nts_42, // 239 - r: DOUBLE_ALOAD(riv,r) 
    nts_21, // 240 - r: DOUBLE_ALOAD(rlv,rlv) 
    nts_36, // 241 - double_load: DOUBLE_ALOAD(rlv,riv) 
    nts_35, // 242 - double_load: DOUBLE_ALOAD(riv,riv) 
    nts_35, // 243 - r: FLOAT_LOAD(riv,riv) 
    nts_21, // 244 - r: FLOAT_LOAD(rlv,rlv) 
    nts_35, // 245 - float_load: FLOAT_LOAD(riv,riv) 
    nts_36, // 246 - float_load: FLOAT_ALOAD(rlv,riv) 
    nts_35, // 247 - r: FLOAT_ALOAD(riv,riv) 
    nts_36, // 248 - r: FLOAT_ALOAD(rlv,riv) 
    nts_42, // 249 - r: FLOAT_ALOAD(riv,r) 
    nts_21, // 250 - r: FLOAT_ALOAD(rlv,rlv) 
    nts_35, // 251 - float_load: FLOAT_ALOAD(riv,riv) 
    nts_18, // 252 - stm: FLOAT_IFCMP(r,r) 
    nts_49, // 253 - stm: FLOAT_IFCMP(r,float_load) 
    nts_50, // 254 - stm: FLOAT_IFCMP(float_load,r) 
    nts_18, // 255 - stm: DOUBLE_IFCMP(r,r) 
    nts_51, // 256 - stm: DOUBLE_IFCMP(r,double_load) 
    nts_52, // 257 - stm: DOUBLE_IFCMP(double_load,r) 
    nts_0,  // 258 - stm: LOWTABLESWITCH(r) 
    nts_3,  // 259 - stm: NULL_CHECK(riv) 
    nts_0,  // 260 - stm: SET_CAUGHT_EXCEPTION(r) 
    nts_0,  // 261 - stm: TRAP_IF(r,INT_CONSTANT) 
    nts_0,  // 262 - stm: TRAP_IF(r,LONG_CONSTANT) 
    nts_15, // 263 - uload8: INT_AND(load8_16_32,INT_CONSTANT) 
    nts_15, // 264 - r: INT_AND(load8_16_32,INT_CONSTANT) 
    nts_15, // 265 - r: INT_2BYTE(load8_16_32) 
    nts_12, // 266 - r: INT_AND(load16_32,INT_CONSTANT) 
    nts_0,  // 267 - stm: PREFETCH(r) 
    nts_0,  // 268 - stm: RETURN(r) 
    nts_0,  // 269 - address1scaledreg: INT_SHL(r,INT_CONSTANT) 
    nts_0,  // 270 - address1reg: INT_ADD(r,LONG_CONSTANT) 
    nts_0,  // 271 - address1reg: INT_MOVE(r) 
    nts_4,  // 272 - address1reg: INT_ADD(address1reg,LONG_CONSTANT) 
    nts_5,  // 273 - address1scaledreg: INT_ADD(address1scaledreg,LONG_CONSTANT) 
    nts_5,  // 274 - address: INT_ADD(address1scaledreg,LONG_CONSTANT) 
    nts_0,  // 275 - address1scaledreg: LONG_SHL(r,INT_CONSTANT) 
    nts_0,  // 276 - address1reg: LONG_ADD(r,LONG_CONSTANT) 
    nts_0,  // 277 - address1reg: LONG_MOVE(r) 
    nts_4,  // 278 - address1reg: LONG_ADD(address1reg,LONG_CONSTANT) 
    nts_5,  // 279 - address1scaledreg: LONG_ADD(address1scaledreg,LONG_CONSTANT) 
    nts_5,  // 280 - address: LONG_ADD(address1scaledreg,LONG_CONSTANT) 
    nts_0,  // 281 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_0,  // 282 - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_0,  // 283 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_11, // 284 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) 
    nts_0,  // 285 - r: BOOLEAN_CMP_INT(r,INT_CONSTANT) 
    nts_11, // 286 - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT) 
    nts_53, // 287 - r: BOOLEAN_CMP_INT(cz,INT_CONSTANT) 
    nts_53, // 288 - boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT) 
    nts_54, // 289 - r: BOOLEAN_CMP_INT(szp,INT_CONSTANT) 
    nts_54, // 290 - boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT) 
    nts_55, // 291 - r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) 
    nts_55, // 292 - boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT) 
    nts_56, // 293 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_56, // 294 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_56, // 295 - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_56, // 296 - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT) 
    nts_0,  // 297 - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) 
    nts_0,  // 298 - boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) 
    nts_0,  // 299 - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) 
    nts_14, // 300 - r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT) 
    nts_0,  // 301 - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT) 
    nts_14, // 302 - r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT) 
    nts_53, // 303 - r: BOOLEAN_CMP_LONG(cz,LONG_CONSTANT) 
    nts_0,  // 304 - r: BOOLEAN_NOT(r) 
    nts_0,  // 305 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_11, // 306 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_0,  // 307 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_11, // 308 - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT))) 
    nts_0,  // 309 - r: INT_2BYTE(r) 
    nts_15, // 310 - r: INT_2BYTE(load8_16_32) 
    nts_0,  // 311 - r: INT_2LONG(r) 
    nts_11, // 312 - r: INT_2LONG(load32) 
    nts_0,  // 313 - r: INT_2ADDRZerExt(r) 
    nts_0,  // 314 - r: INT_2SHORT(r) 
    nts_12, // 315 - r: INT_2SHORT(load16_32) 
    nts_12, // 316 - sload16: INT_2SHORT(load16_32) 
    nts_0,  // 317 - szpr: INT_2USHORT(r) 
    nts_12, // 318 - uload16: INT_2USHORT(load16_32) 
    nts_12, // 319 - r: INT_2USHORT(load16_32) 
    nts_0,  // 320 - stm: INT_IFCMP(r,INT_CONSTANT) 
    nts_13, // 321 - stm: INT_IFCMP(load8,INT_CONSTANT) 
    nts_8,  // 322 - stm: INT_IFCMP(sload16,INT_CONSTANT) 
    nts_56, // 323 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) 
    nts_56, // 324 - stm: INT_IFCMP(boolcmp,INT_CONSTANT) 
    nts_53, // 325 - stm: INT_IFCMP(cz,INT_CONSTANT) 
    nts_54, // 326 - stm: INT_IFCMP(szp,INT_CONSTANT) 
    nts_55, // 327 - stm: INT_IFCMP(bittest,INT_CONSTANT) 
    nts_57, // 328 - r: INT_LOAD(address,LONG_CONSTANT) 
    nts_3,  // 329 - r: INT_MOVE(riv) 
    nts_1,  // 330 - czr: INT_MOVE(czr) 
    nts_53, // 331 - cz: INT_MOVE(cz) 
    nts_2,  // 332 - szpr: INT_MOVE(szpr) 
    nts_54, // 333 - szp: INT_MOVE(szp) 
    nts_6,  // 334 - sload8: INT_MOVE(sload8) 
    nts_7,  // 335 - uload8: INT_MOVE(uload8) 
    nts_13, // 336 - load8: INT_MOVE(load8) 
    nts_8,  // 337 - sload16: INT_MOVE(sload16) 
    nts_9,  // 338 - uload16: INT_MOVE(uload16) 
    nts_10, // 339 - load16: INT_MOVE(load16) 
    nts_11, // 340 - load32: INT_MOVE(load32) 
    nts_0,  // 341 - szpr: INT_NEG(r) 
    nts_0,  // 342 - r: INT_NOT(r) 
    nts_0,  // 343 - szpr: INT_SHL(r,INT_CONSTANT) 
    nts_0,  // 344 - r: INT_SHL(r,INT_CONSTANT) 
    nts_3,  // 345 - szpr: INT_SHR(riv,INT_CONSTANT) 
    nts_3,  // 346 - szpr: INT_USHR(riv,INT_CONSTANT) 
    nts_57, // 347 - r: LONG_ADD(address,LONG_CONSTANT) 
    nts_57, // 348 - r: LONG_MOVE(address) 
    nts_0,  // 349 - r: LONG_2INT(r) 
    nts_14, // 350 - r: LONG_2INT(load64) 
    nts_14, // 351 - load32: LONG_2INT(load64) 
    nts_0,  // 352 - stm: LONG_IFCMP(r,LONG_CONSTANT) 
    nts_57, // 353 - r: LONG_LOAD(address,LONG_CONSTANT) 
    nts_58, // 354 - r: LONG_MOVE(rlv) 
    nts_3,  // 355 - r: LONG_MOVE(riv) 
    nts_14, // 356 - load64: LONG_MOVE(load64) 
    nts_0,  // 357 - szpr: LONG_NEG(r) 
    nts_0,  // 358 - r: LONG_NOT(r) 
    nts_0,  // 359 - szpr: LONG_SHL(r,INT_CONSTANT) 
    nts_0,  // 360 - r: LONG_SHL(r,INT_CONSTANT) 
    nts_58, // 361 - szpr: LONG_SHR(rlv,LONG_CONSTANT) 
    nts_58, // 362 - szpr: LONG_USHR(rlv,LONG_CONSTANT) 
    nts_0,  // 363 - r: FLOAT_NEG(r) 
    nts_0,  // 364 - r: DOUBLE_NEG(r) 
    nts_0,  // 365 - r: FLOAT_SQRT(r) 
    nts_0,  // 366 - r: DOUBLE_SQRT(r) 
    nts_0,  // 367 - r: LONG_2FLOAT(r) 
    nts_0,  // 368 - r: LONG_2DOUBLE(r) 
    nts_0,  // 369 - r: FLOAT_MOVE(r) 
    nts_0,  // 370 - r: DOUBLE_MOVE(r) 
    nts_3,  // 371 - r: INT_2FLOAT(riv) 
    nts_11, // 372 - r: INT_2FLOAT(load32) 
    nts_3,  // 373 - r: INT_2DOUBLE(riv) 
    nts_11, // 374 - r: INT_2DOUBLE(load32) 
    nts_0,  // 375 - r: FLOAT_2DOUBLE(r) 
    nts_59, // 376 - r: FLOAT_2DOUBLE(float_load) 
    nts_0,  // 377 - r: DOUBLE_2FLOAT(r) 
    nts_60, // 378 - r: DOUBLE_2FLOAT(double_load) 
    nts_0,  // 379 - r: FLOAT_2INT(r) 
    nts_0,  // 380 - r: FLOAT_2LONG(r) 
    nts_0,  // 381 - r: DOUBLE_2INT(r) 
    nts_0,  // 382 - r: DOUBLE_2LONG(r) 
    nts_0,  // 383 - r: FLOAT_AS_INT_BITS(r) 
    nts_59, // 384 - load32: FLOAT_AS_INT_BITS(float_load) 
    nts_0,  // 385 - r: DOUBLE_AS_LONG_BITS(r) 
    nts_60, // 386 - load64: DOUBLE_AS_LONG_BITS(double_load) 
    nts_3,  // 387 - r: INT_BITS_AS_FLOAT(riv) 
    nts_11, // 388 - float_load: INT_BITS_AS_FLOAT(load32) 
    nts_58, // 389 - r: LONG_BITS_AS_DOUBLE(rlv) 
    nts_14, // 390 - double_load: LONG_BITS_AS_DOUBLE(load64) 
    nts_61, // 391 - r: MATERIALIZE_FP_CONSTANT(any) 
    nts_61, // 392 - float_load: MATERIALIZE_FP_CONSTANT(any) 
    nts_61, // 393 - double_load: MATERIALIZE_FP_CONSTANT(any) 
    nts_15, // 394 - r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT) 
    nts_12, // 395 - r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 396 - bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 397 - bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 398 - r: LONG_AND(INT_2LONG(r),LONG_CONSTANT) 
    nts_11, // 399 - r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT) 
    nts_0,  // 400 - szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_0,  // 401 - r: LONG_2INT(LONG_USHR(r,INT_CONSTANT)) 
    nts_0,  // 402 - r: LONG_2INT(LONG_SHR(r,INT_CONSTANT)) 
    nts_14, // 403 - r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) 
    nts_14, // 404 - r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) 
    nts_14, // 405 - load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT)) 
    nts_14, // 406 - load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT)) 
    nts_0,  // 407 - szpr: LONG_SHL(LONG_SHR(r,INT_CONSTANT),INT_CONSTANT) 
    nts_62, // 408 - stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_63, // 409 - stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv)) 
    nts_64, // 410 - stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv)) 
    nts_65, // 411 - stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv)) 
    nts_62, // 412 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_63, // 413 - stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv)) 
    nts_66, // 414 - stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r)) 
    nts_62, // 415 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv)) 
    nts_66, // 416 - stm: INT_ASTORE(riv,OTHER_OPERAND(r,r)) 
    nts_65, // 417 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv)) 
    nts_67, // 418 - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv)) 
    nts_68, // 419 - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv)) 
    nts_69, // 420 - stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv)) 
    nts_70, // 421 - stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_71, // 422 - stm: LONG_ASTORE(r,OTHER_OPERAND(r,r)) 
    nts_72, // 423 - stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv)) 
    nts_72, // 424 - stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv)) 
    nts_65, // 425 - stm: BYTE_STORE(riv,OTHER_OPERAND(rlv,rlv)) 
    nts_73, // 426 - stm: BYTE_STORE(load8,OTHER_OPERAND(rlv,rlv)) 
    nts_67, // 427 - stm: BYTE_ASTORE(riv,OTHER_OPERAND(rlv,riv)) 
    nts_74, // 428 - stm: BYTE_ASTORE(load8,OTHER_OPERAND(rlv,riv)) 
    nts_75, // 429 - r: CMP_CMOV(r,OTHER_OPERAND(riv,any)) 
    nts_76, // 430 - r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any)) 
    nts_77, // 431 - r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any)) 
    nts_78, // 432 - r: CMP_CMOV(load32,OTHER_OPERAND(riv,any)) 
    nts_79, // 433 - r: CMP_CMOV(riv,OTHER_OPERAND(load32,any)) 
    nts_65, // 434 - stm: INT_STORE(riv,OTHER_OPERAND(rlv,rlv)) 
    nts_80, // 435 - stm: INT_STORE(riv,OTHER_OPERAND(rlv,address1scaledreg)) 
    nts_81, // 436 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,rlv)) 
    nts_82, // 437 - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg)) 
    nts_83, // 438 - stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg)) 
    nts_84, // 439 - r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any)) 
    nts_85, // 440 - r: LCMP_CMOV(load64,OTHER_OPERAND(rlv,any)) 
    nts_86, // 441 - r: LCMP_CMOV(rlv,OTHER_OPERAND(load64,any)) 
    nts_64, // 442 - stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,rlv)) 
    nts_87, // 443 - stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,address1scaledreg)) 
    nts_88, // 444 - stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,rlv)) 
    nts_89, // 445 - stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,address1reg)) 
    nts_90, // 446 - stm: LONG_STORE(rlv,OTHER_OPERAND(address1reg,address1scaledreg)) 
    nts_69, // 447 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv)) 
    nts_91, // 448 - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_92, // 449 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_70, // 450 - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_69, // 451 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv)) 
    nts_92, // 452 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_91, // 453 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_70, // 454 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_71, // 455 - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r)) 
    nts_69, // 456 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv)) 
    nts_70, // 457 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_92, // 458 - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_91, // 459 - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_69, // 460 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv)) 
    nts_92, // 461 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv)) 
    nts_91, // 462 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv)) 
    nts_70, // 463 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv)) 
    nts_71, // 464 - stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r)) 
    nts_93, // 465 - r: FCMP_CMOV(r,OTHER_OPERAND(r,any)) 
    nts_94, // 466 - r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any)) 
    nts_95, // 467 - r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any)) 
    nts_96, // 468 - r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any)) 
    nts_97, // 469 - r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any)) 
    nts_93, // 470 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,any)) 
    nts_94, // 471 - r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any)) 
    nts_95, // 472 - r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any)) 
    nts_98, // 473 - stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv)) 
    nts_99, // 474 - stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv)) 
    nts_98, // 475 - stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv)) 
    nts_99, // 476 - stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv)) 
    nts_35, // 477 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv)) 
    nts_36, // 478 - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv)) 
    nts_61, // 479 - r: CALL(BRANCH_TARGET,any) 
    nts_61, // 480 - r: CALL(INT_CONSTANT,any) 
    nts_61, // 481 - r: SYSCALL(INT_CONSTANT,any) 
    nts_100, // 482 - r: CALL(INT_LOAD(riv,riv),any) 
    nts_101, // 483 - r: CALL(LONG_LOAD(rlv,rlv),any) 
    nts_100, // 484 - r: SYSCALL(INT_LOAD(riv,riv),any) 
    nts_102, // 485 - r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))) 
    nts_103, // 486 - r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) 
    nts_104, // 487 - r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv))) 
    nts_105, // 488 - r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) 
    nts_106, // 489 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))) 
    nts_107, // 490 - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))) 
    nts_108, // 491 - r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))) 
    nts_109, // 492 - r: ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))) 
    nts_110, // 493 - r: ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))) 
    nts_111, // 494 - r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))) 
    nts_112, // 495 - r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))) 
    nts_113, // 496 - r: ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))) 
    nts_114, // 497 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load))) 
    nts_115, // 498 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load))) 
    nts_116, // 499 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r))) 
    nts_117, // 500 - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r))) 
    nts_118, // 501 - r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))) 
    nts_119, // 502 - r: ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))) 
    nts_118, // 503 - r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))) 
    nts_119, // 504 - r: ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))) 
    nts_102, // 505 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_105, // 506 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_106, // 507 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_107, // 508 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_108, // 509 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_102, // 510 - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_105, // 511 - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_106, // 512 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_107, // 513 - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_108, // 514 - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_109, // 515 - stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_110, // 516 - stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_111, // 517 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_112, // 518 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_113, // 519 - stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_109, // 520 - stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_110, // 521 - stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_111, // 522 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_112, // 523 - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_113, // 524 - stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_118, // 525 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_118, // 526 - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_119, // 527 - stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_119, // 528 - stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_118, // 529 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_118, // 530 - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT) 
    nts_119, // 531 - stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_119, // 532 - stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT) 
    nts_18, // 533 - bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_43, // 534 - bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_18, // 535 - bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_43, // 536 - bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT) 
    nts_42, // 537 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r) 
    nts_28, // 538 - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32) 
    nts_18, // 539 - bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) 
    nts_43, // 540 - bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT))) 
    nts_109, // 541 - stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_120, // 542 - stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv,riv)) 
    nts_102, // 543 - stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 544 - stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 545 - stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 546 - stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 547 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 548 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 549 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 550 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 551 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 552 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 553 - stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 554 - stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 555 - stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 556 - stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_102, // 557 - stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 558 - stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 559 - stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 560 - stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 561 - stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_102, // 562 - stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv)) 
    nts_22, // 563 - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_121, // 564 - r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_122, // 565 - r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_123, // 566 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_123, // 567 - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_124, // 568 - r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_125, // 569 - r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_126, // 570 - r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_22, // 571 - r: LCMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any)) 
    nts_69, // 572 - stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 573 - stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 574 - stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 575 - stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 576 - stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 577 - stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 578 - stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) 
    nts_69, // 579 - stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv)) 
    nts_127, // 580 - stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 581 - stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 582 - stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 583 - stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 584 - stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 585 - stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 586 - stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 587 - stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 588 - stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_127, // 589 - stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv)) 
    nts_128, // 590 - stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 591 - stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 592 - stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 593 - stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 594 - stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 595 - stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 596 - stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 597 - stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 598 - stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 599 - stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv)) 
    nts_127, // 600 - stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_127, // 601 - stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_129, // 602 - stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_129, // 603 - stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_129, // 604 - stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_129, // 605 - stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_127, // 606 - stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_127, // 607 - stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_129, // 608 - stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_129, // 609 - stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv)) 
    nts_128, // 610 - stm: LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 611 - stm: LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_130, // 612 - stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_130, // 613 - stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_130, // 614 - stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_130, // 615 - stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 616 - stm: LONG_STORE(LONG_SUB(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_128, // 617 - stm: LONG_ASTORE(LONG_SUB(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_130, // 618 - stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_130, // 619 - stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv)) 
    nts_18, // 620 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) 
    nts_18, // 621 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) 
    nts_18, // 622 - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT)) 
    nts_18, // 623 - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT)) 
    nts_131, // 624 - r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT))) 
    nts_131, // 625 - r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT))) 
    nts_131, // 626 - r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT))) 
    nts_131, // 627 - r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT))) 
    nts_42, // 628 - szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT)) 
    nts_42, // 629 - szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT)) 
    nts_132, // 630 - stm: INT_STORE(riv,OTHER_OPERAND(address,LONG_CONSTANT)) 
    nts_42, // 631 - szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT)) 
    nts_44, // 632 - szpr: LONG_SHL(rlv,INT_AND(r,INT_CONSTANT)) 
    nts_44, // 633 - szpr: LONG_SHR(rlv,INT_AND(r,LONG_CONSTANT)) 
    nts_133, // 634 - stm: LONG_STORE(rlv,OTHER_OPERAND(address,LONG_CONSTANT)) 
    nts_44, // 635 - szpr: LONG_USHR(rlv,LONG_AND(r,LONG_CONSTANT)) 
    nts_134, // 636 - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 637 - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 638 - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 639 - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 640 - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 641 - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 642 - stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 643 - stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 644 - stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 645 - stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 646 - stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_134, // 647 - stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv)) 
    nts_71, // 648 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_71, // 649 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_71, // 650 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
    nts_71, // 651 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
    nts_71, // 652 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_71, // 653 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_71, // 654 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_71, // 655 - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_71, // 656 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_71, // 657 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r))) 
    nts_71, // 658 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_71, // 659 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r))) 
    nts_71, // 660 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_71, // 661 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r)))) 
    nts_71, // 662 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
    nts_71, // 663 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r)))) 
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
    2,  // 92 - LONG_DIV
    2,  // 93 - UNSIGNED_DIV_64_32
    2,  // 94 - UNSIGNED_REM_64_32
    2,  // 95 - FLOAT_DIV
    2,  // 96 - DOUBLE_DIV
    2,  // 97 - INT_REM
    2,  // 98 - LONG_REM
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
    1,  // 130 - INT_2ADDRZerExt
    -1, // 131 - LONG_2ADDR
    -1, // 132 - ADDR_2INT
    -1, // 133 - ADDR_2LONG
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
      27, // [1][2] - stm: IG_PATCH_POINT
      28, // [1][3] - stm: UNINT_BEGIN
      29, // [1][4] - stm: UNINT_END
      30, // [1][5] - stm: YIELDPOINT_PROLOGUE
      31, // [1][6] - stm: YIELDPOINT_EPILOGUE
      32, // [1][7] - stm: YIELDPOINT_BACKEDGE
      258, // [1][8] - stm: LOWTABLESWITCH(r)
      34, // [1][9] - stm: RESOLVE
      35, // [1][10] - stm: NOP
      259, // [1][11] - stm: NULL_CHECK(riv)
      38, // [1][12] - stm: IR_PROLOGUE
      260, // [1][13] - stm: SET_CAUGHT_EXCEPTION(r)
      40, // [1][14] - stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
      41, // [1][15] - stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
      42, // [1][16] - stm: TRAP
      261, // [1][17] - stm: TRAP_IF(r,INT_CONSTANT)
      262, // [1][18] - stm: TRAP_IF(r,LONG_CONSTANT)
      55, // [1][19] - stm: TRAP_IF(r,r)
      56, // [1][20] - stm: TRAP_IF(load32,riv)
      57, // [1][21] - stm: TRAP_IF(riv,load32)
      408, // [1][22] - stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
      409, // [1][23] - stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
      410, // [1][24] - stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      411, // [1][25] - stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      412, // [1][26] - stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      413, // [1][27] - stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
      414, // [1][28] - stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
      415, // [1][29] - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      416, // [1][30] - stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
      417, // [1][31] - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
      418, // [1][32] - stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      419, // [1][33] - stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
      420, // [1][34] - stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
      421, // [1][35] - stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      422, // [1][36] - stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
      477, // [1][37] - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
      478, // [1][38] - stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
      43, // [1][39] - stm: GOTO
      267, // [1][40] - stm: PREFETCH(r)
      44, // [1][41] - stm: WRITE_FLOOR
      45, // [1][42] - stm: READ_CEILING
      46, // [1][43] - stm: FENCE
      47, // [1][44] - stm: PAUSE
      48, // [1][45] - stm: ILLEGAL_INSTRUCTION
      49, // [1][46] - stm: RETURN(NULL)
      50, // [1][47] - stm: RETURN(INT_CONSTANT)
      268, // [1][48] - stm: RETURN(r)
      51, // [1][49] - stm: RETURN(LONG_CONSTANT)
      61, // [1][50] - stm: YIELDPOINT_OSR(any,any)
      505, // [1][51] - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      506, // [1][52] - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      507, // [1][53] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      508, // [1][54] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      509, // [1][55] - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      525, // [1][56] - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      529, // [1][57] - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      510, // [1][58] - stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      511, // [1][59] - stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      512, // [1][60] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      513, // [1][61] - stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      514, // [1][62] - stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      526, // [1][63] - stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      530, // [1][64] - stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      515, // [1][65] - stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      516, // [1][66] - stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      517, // [1][67] - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      518, // [1][68] - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      519, // [1][69] - stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      527, // [1][70] - stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      531, // [1][71] - stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      520, // [1][72] - stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      521, // [1][73] - stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      522, // [1][74] - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      523, // [1][75] - stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      524, // [1][76] - stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      528, // [1][77] - stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      532, // [1][78] - stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      423, // [1][79] - stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
      424, // [1][80] - stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
      541, // [1][81] - stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      542, // [1][82] - stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv,riv))
      425, // [1][83] - stm: BYTE_STORE(riv,OTHER_OPERAND(rlv,rlv))
      426, // [1][84] - stm: BYTE_STORE(load8,OTHER_OPERAND(rlv,rlv))
      427, // [1][85] - stm: BYTE_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      428, // [1][86] - stm: BYTE_ASTORE(load8,OTHER_OPERAND(rlv,riv))
      572, // [1][87] - stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      573, // [1][88] - stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      574, // [1][89] - stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      575, // [1][90] - stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      576, // [1][91] - stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      577, // [1][92] - stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      580, // [1][93] - stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      600, // [1][94] - stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      581, // [1][95] - stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      601, // [1][96] - stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      582, // [1][97] - stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      602, // [1][98] - stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      583, // [1][99] - stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      603, // [1][100] - stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      98, // [1][101] - stm: INT_IFCMP(r,riv)
      320, // [1][102] - stm: INT_IFCMP(r,INT_CONSTANT)
      321, // [1][103] - stm: INT_IFCMP(load8,INT_CONSTANT)
      99, // [1][104] - stm: INT_IFCMP(uload8,r)
      100, // [1][105] - stm: INT_IFCMP(r,uload8)
      322, // [1][106] - stm: INT_IFCMP(sload16,INT_CONSTANT)
      101, // [1][107] - stm: INT_IFCMP(load32,riv)
      102, // [1][108] - stm: INT_IFCMP(r,load32)
      323, // [1][109] - stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      324, // [1][110] - stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      325, // [1][111] - stm: INT_IFCMP(cz,INT_CONSTANT)
      326, // [1][112] - stm: INT_IFCMP(szp,INT_CONSTANT)
      327, // [1][113] - stm: INT_IFCMP(bittest,INT_CONSTANT)
      103, // [1][114] - stm: INT_IFCMP2(r,riv)
      104, // [1][115] - stm: INT_IFCMP2(load32,riv)
      105, // [1][116] - stm: INT_IFCMP2(riv,load32)
      543, // [1][117] - stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      544, // [1][118] - stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      545, // [1][119] - stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      546, // [1][120] - stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      584, // [1][121] - stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      604, // [1][122] - stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      585, // [1][123] - stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      605, // [1][124] - stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      636, // [1][125] - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      547, // [1][126] - stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      637, // [1][127] - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      548, // [1][128] - stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      638, // [1][129] - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      549, // [1][130] - stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      639, // [1][131] - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      550, // [1][132] - stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      434, // [1][133] - stm: INT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      435, // [1][134] - stm: INT_STORE(riv,OTHER_OPERAND(rlv,address1scaledreg))
      436, // [1][135] - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,rlv))
      437, // [1][136] - stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
      438, // [1][137] - stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
      630, // [1][138] - stm: INT_STORE(riv,OTHER_OPERAND(address,LONG_CONSTANT))
      586, // [1][139] - stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      606, // [1][140] - stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      587, // [1][141] - stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      607, // [1][142] - stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      640, // [1][143] - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      551, // [1][144] - stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      641, // [1][145] - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      552, // [1][146] - stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      588, // [1][147] - stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      608, // [1][148] - stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      589, // [1][149] - stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      609, // [1][150] - stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      578, // [1][151] - stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      579, // [1][152] - stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      590, // [1][153] - stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      610, // [1][154] - stm: LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      591, // [1][155] - stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      611, // [1][156] - stm: LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      592, // [1][157] - stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      612, // [1][158] - stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      593, // [1][159] - stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      613, // [1][160] - stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      180, // [1][161] - stm: LONG_IFCMP(rlv,rlv)
      352, // [1][162] - stm: LONG_IFCMP(r,LONG_CONSTANT)
      553, // [1][163] - stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      554, // [1][164] - stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      555, // [1][165] - stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      556, // [1][166] - stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      594, // [1][167] - stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      614, // [1][168] - stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      595, // [1][169] - stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      615, // [1][170] - stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      642, // [1][171] - stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      557, // [1][172] - stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      643, // [1][173] - stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      558, // [1][174] - stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      644, // [1][175] - stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      559, // [1][176] - stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      645, // [1][177] - stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      560, // [1][178] - stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      442, // [1][179] - stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      443, // [1][180] - stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,address1scaledreg))
      444, // [1][181] - stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,rlv))
      445, // [1][182] - stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,address1reg))
      446, // [1][183] - stm: LONG_STORE(rlv,OTHER_OPERAND(address1reg,address1scaledreg))
      634, // [1][184] - stm: LONG_STORE(rlv,OTHER_OPERAND(address,LONG_CONSTANT))
      596, // [1][185] - stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      616, // [1][186] - stm: LONG_STORE(LONG_SUB(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      597, // [1][187] - stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      617, // [1][188] - stm: LONG_ASTORE(LONG_SUB(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      646, // [1][189] - stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      561, // [1][190] - stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      647, // [1][191] - stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      562, // [1][192] - stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      598, // [1][193] - stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      618, // [1][194] - stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      599, // [1][195] - stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      619, // [1][196] - stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      447, // [1][197] - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
      448, // [1][198] - stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
      449, // [1][199] - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
      450, // [1][200] - stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
      451, // [1][201] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
      452, // [1][202] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
      453, // [1][203] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
      454, // [1][204] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      455, // [1][205] - stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
      456, // [1][206] - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
      457, // [1][207] - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
      458, // [1][208] - stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
      459, // [1][209] - stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
      460, // [1][210] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
      461, // [1][211] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
      462, // [1][212] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
      463, // [1][213] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      464, // [1][214] - stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
      53, // [1][215] - stm: CLEAR_FLOATING_POINT_STATE
      252, // [1][216] - stm: FLOAT_IFCMP(r,r)
      253, // [1][217] - stm: FLOAT_IFCMP(r,float_load)
      254, // [1][218] - stm: FLOAT_IFCMP(float_load,r)
      255, // [1][219] - stm: DOUBLE_IFCMP(r,r)
      256, // [1][220] - stm: DOUBLE_IFCMP(r,double_load)
      257, // [1][221] - stm: DOUBLE_IFCMP(double_load,r)
      473, // [1][222] - stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
      474, // [1][223] - stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
      475, // [1][224] - stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
      476, // [1][225] - stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
    },
    { // r_NT
      0, // [2][0]
      21, // [2][1] - r: REGISTER
      2, // [2][2] - r: czr
      4, // [2][3] - r: szpr
      33, // [2][4] - r: FRAMESIZE
      36, // [2][5] - r: GUARD_MOVE
      37, // [2][6] - r: GUARD_COMBINE
      39, // [2][7] - r: GET_CAUGHT_EXCEPTION
      264, // [2][8] - r: INT_AND(load8_16_32,INT_CONSTANT)
      265, // [2][9] - r: INT_2BYTE(load8_16_32)
      394, // [2][10] - r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
      266, // [2][11] - r: INT_AND(load16_32,INT_CONSTANT)
      395, // [2][12] - r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
      58, // [2][13] - r: LONG_CMP(rlv,rlv)
      59, // [2][14] - r: CALL(r,any)
      479, // [2][15] - r: CALL(BRANCH_TARGET,any)
      482, // [2][16] - r: CALL(INT_LOAD(riv,riv),any)
      480, // [2][17] - r: CALL(INT_CONSTANT,any)
      483, // [2][18] - r: CALL(LONG_LOAD(rlv,rlv),any)
      60, // [2][19] - r: SYSCALL(r,any)
      484, // [2][20] - r: SYSCALL(INT_LOAD(riv,riv),any)
      481, // [2][21] - r: SYSCALL(INT_CONSTANT,any)
      52, // [2][22] - r: GET_TIME_BASE
      485, // [2][23] - r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
      486, // [2][24] - r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      487, // [2][25] - r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      488, // [2][26] - r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      489, // [2][27] - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
      490, // [2][28] - r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
      491, // [2][29] - r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      501, // [2][30] - r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
      503, // [2][31] - r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
      492, // [2][32] - r: ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv)))
      493, // [2][33] - r: ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
      494, // [2][34] - r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv)))
      495, // [2][35] - r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv)))
      496, // [2][36] - r: ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
      502, // [2][37] - r: ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv)))
      504, // [2][38] - r: ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv)))
      72, // [2][39] - r: BOOLEAN_CMP_INT(r,riv)
      281, // [2][40] - r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      283, // [2][41] - r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      284, // [2][42] - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      285, // [2][43] - r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      286, // [2][44] - r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      287, // [2][45] - r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      289, // [2][46] - r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      291, // [2][47] - r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      293, // [2][48] - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      295, // [2][49] - r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      74, // [2][50] - r: BOOLEAN_CMP_INT(load32,riv)
      76, // [2][51] - r: BOOLEAN_CMP_INT(r,load32)
      78, // [2][52] - r: BOOLEAN_CMP_LONG(r,rlv)
      297, // [2][53] - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      299, // [2][54] - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      300, // [2][55] - r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
      301, // [2][56] - r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      302, // [2][57] - r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
      303, // [2][58] - r: BOOLEAN_CMP_LONG(cz,LONG_CONSTANT)
      80, // [2][59] - r: BOOLEAN_CMP_LONG(load64,rlv)
      82, // [2][60] - r: BOOLEAN_CMP_LONG(r,load64)
      304, // [2][61] - r: BOOLEAN_NOT(r)
      429, // [2][62] - r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
      563, // [2][63] - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      305, // [2][64] - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      306, // [2][65] - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      307, // [2][66] - r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      308, // [2][67] - r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      564, // [2][68] - r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
      430, // [2][69] - r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
      431, // [2][70] - r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
      565, // [2][71] - r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
      432, // [2][72] - r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
      433, // [2][73] - r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
      566, // [2][74] - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      567, // [2][75] - r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      568, // [2][76] - r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
      569, // [2][77] - r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
      570, // [2][78] - r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
      309, // [2][79] - r: INT_2BYTE(r)
      310, // [2][80] - r: INT_2BYTE(load8_16_32)
      311, // [2][81] - r: INT_2LONG(r)
      312, // [2][82] - r: INT_2LONG(load32)
      398, // [2][83] - r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
      399, // [2][84] - r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
      313, // [2][85] - r: INT_2ADDRZerExt(r)
      314, // [2][86] - r: INT_2SHORT(r)
      315, // [2][87] - r: INT_2SHORT(load16_32)
      319, // [2][88] - r: INT_2USHORT(load16_32)
      85, // [2][89] - r: INT_ADD(r,riv)
      94, // [2][90] - r: INT_DIV(riv,riv)
      95, // [2][91] - r: INT_DIV(riv,load32)
      96, // [2][92] - r: UNSIGNED_DIV_64_32(rlv,riv)
      97, // [2][93] - r: UNSIGNED_DIV_64_32(rlv,load32)
      106, // [2][94] - r: INT_LOAD(rlv,rlv)
      107, // [2][95] - r: INT_LOAD(rlv,address1scaledreg)
      108, // [2][96] - r: INT_LOAD(address1scaledreg,rlv)
      109, // [2][97] - r: INT_LOAD(address1scaledreg,address1reg)
      110, // [2][98] - r: INT_LOAD(address1reg,address1scaledreg)
      328, // [2][99] - r: INT_LOAD(address,LONG_CONSTANT)
      111, // [2][100] - r: INT_ALOAD(rlv,riv)
      329, // [2][101] - r: INT_MOVE(riv)
      112, // [2][102] - r: INT_MUL(r,riv)
      113, // [2][103] - r: INT_MUL(r,load32)
      114, // [2][104] - r: INT_MUL(load32,riv)
      342, // [2][105] - r: INT_NOT(r)
      118, // [2][106] - r: INT_REM(riv,riv)
      119, // [2][107] - r: INT_REM(riv,load32)
      120, // [2][108] - r: UNSIGNED_REM_64_32(rlv,riv)
      121, // [2][109] - r: UNSIGNED_REM_64_32(rlv,load32)
      620, // [2][110] - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      621, // [2][111] - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      622, // [2][112] - r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      623, // [2][113] - r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      624, // [2][114] - r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      626, // [2][115] - r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
      627, // [2][116] - r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
      625, // [2][117] - r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      344, // [2][118] - r: INT_SHL(r,INT_CONSTANT)
      125, // [2][119] - r: INT_SUB(riv,r)
      126, // [2][120] - r: INT_SUB(load32,r)
      439, // [2][121] - r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
      571, // [2][122] - r: LCMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      440, // [2][123] - r: LCMP_CMOV(load64,OTHER_OPERAND(rlv,any))
      441, // [2][124] - r: LCMP_CMOV(rlv,OTHER_OPERAND(load64,any))
      133, // [2][125] - r: LONG_ADD(address1scaledreg,r)
      134, // [2][126] - r: LONG_ADD(r,address1scaledreg)
      135, // [2][127] - r: LONG_ADD(address1scaledreg,address1reg)
      136, // [2][128] - r: LONG_ADD(address1reg,address1scaledreg)
      347, // [2][129] - r: LONG_ADD(address,LONG_CONSTANT)
      348, // [2][130] - r: LONG_MOVE(address)
      137, // [2][131] - r: BYTE_LOAD(rlv,rlv)
      139, // [2][132] - r: BYTE_ALOAD(rlv,riv)
      140, // [2][133] - r: BYTE_ALOAD(rlv,r)
      142, // [2][134] - r: UBYTE_LOAD(rlv,rlv)
      144, // [2][135] - r: UBYTE_ALOAD(rlv,riv)
      145, // [2][136] - r: UBYTE_ALOAD(rlv,r)
      147, // [2][137] - r: SHORT_LOAD(rlv,rlv)
      149, // [2][138] - r: SHORT_ALOAD(rlv,riv)
      150, // [2][139] - r: SHORT_ALOAD(rlv,r)
      152, // [2][140] - r: USHORT_LOAD(rlv,rlv)
      154, // [2][141] - r: USHORT_ALOAD(rlv,riv)
      155, // [2][142] - r: USHORT_ALOAD(rlv,r)
      349, // [2][143] - r: LONG_2INT(r)
      350, // [2][144] - r: LONG_2INT(load64)
      401, // [2][145] - r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
      402, // [2][146] - r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
      403, // [2][147] - r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      404, // [2][148] - r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      165, // [2][149] - r: LONG_ADD(r,rlv)
      175, // [2][150] - r: LONG_DIV(rlv,rlv)
      176, // [2][151] - r: LONG_DIV(rlv,riv)
      177, // [2][152] - r: LONG_DIV(riv,rlv)
      178, // [2][153] - r: LONG_DIV(rlv,load64)
      179, // [2][154] - r: LONG_DIV(load64,rlv)
      181, // [2][155] - r: LONG_LOAD(rlv,rlv)
      182, // [2][156] - r: LONG_LOAD(rlv,address1scaledreg)
      183, // [2][157] - r: LONG_LOAD(address1scaledreg,rlv)
      184, // [2][158] - r: LONG_LOAD(address1scaledreg,address1reg)
      185, // [2][159] - r: LONG_LOAD(address1reg,address1scaledreg)
      353, // [2][160] - r: LONG_LOAD(address,LONG_CONSTANT)
      186, // [2][161] - r: LONG_ALOAD(rlv,riv)
      187, // [2][162] - r: LONG_ALOAD(rlv,r)
      354, // [2][163] - r: LONG_MOVE(rlv)
      355, // [2][164] - r: LONG_MOVE(riv)
      188, // [2][165] - r: LONG_MUL(r,rlv)
      189, // [2][166] - r: INT_MUL(r,load64)
      190, // [2][167] - r: INT_MUL(load64,rlv)
      358, // [2][168] - r: LONG_NOT(r)
      194, // [2][169] - r: LONG_REM(rlv,rlv)
      195, // [2][170] - r: LONG_REM(rlv,riv)
      196, // [2][171] - r: LONG_REM(riv,rlv)
      197, // [2][172] - r: LONG_REM(rlv,load64)
      198, // [2][173] - r: LONG_REM(load64,rlv)
      360, // [2][174] - r: LONG_SHL(r,INT_CONSTANT)
      202, // [2][175] - r: LONG_SUB(rlv,r)
      203, // [2][176] - r: LONG_SUB(load64,r)
      210, // [2][177] - r: FLOAT_ADD(r,r)
      211, // [2][178] - r: FLOAT_ADD(r,float_load)
      212, // [2][179] - r: FLOAT_ADD(float_load,r)
      213, // [2][180] - r: DOUBLE_ADD(r,r)
      214, // [2][181] - r: DOUBLE_ADD(r,double_load)
      215, // [2][182] - r: DOUBLE_ADD(double_load,r)
      216, // [2][183] - r: FLOAT_SUB(r,r)
      217, // [2][184] - r: FLOAT_SUB(r,float_load)
      218, // [2][185] - r: DOUBLE_SUB(r,r)
      219, // [2][186] - r: DOUBLE_SUB(r,double_load)
      220, // [2][187] - r: FLOAT_MUL(r,r)
      221, // [2][188] - r: FLOAT_MUL(r,float_load)
      222, // [2][189] - r: FLOAT_MUL(float_load,r)
      223, // [2][190] - r: DOUBLE_MUL(r,r)
      224, // [2][191] - r: DOUBLE_MUL(r,double_load)
      225, // [2][192] - r: DOUBLE_MUL(double_load,r)
      226, // [2][193] - r: FLOAT_DIV(r,r)
      227, // [2][194] - r: FLOAT_DIV(r,float_load)
      228, // [2][195] - r: DOUBLE_DIV(r,r)
      229, // [2][196] - r: DOUBLE_DIV(r,double_load)
      363, // [2][197] - r: FLOAT_NEG(r)
      364, // [2][198] - r: DOUBLE_NEG(r)
      365, // [2][199] - r: FLOAT_SQRT(r)
      366, // [2][200] - r: DOUBLE_SQRT(r)
      230, // [2][201] - r: FLOAT_REM(r,r)
      231, // [2][202] - r: DOUBLE_REM(r,r)
      367, // [2][203] - r: LONG_2FLOAT(r)
      368, // [2][204] - r: LONG_2DOUBLE(r)
      369, // [2][205] - r: FLOAT_MOVE(r)
      370, // [2][206] - r: DOUBLE_MOVE(r)
      232, // [2][207] - r: DOUBLE_LOAD(riv,riv)
      233, // [2][208] - r: DOUBLE_LOAD(riv,rlv)
      234, // [2][209] - r: DOUBLE_LOAD(rlv,rlv)
      236, // [2][210] - r: DOUBLE_ALOAD(riv,riv)
      237, // [2][211] - r: DOUBLE_ALOAD(rlv,riv)
      239, // [2][212] - r: DOUBLE_ALOAD(riv,r)
      240, // [2][213] - r: DOUBLE_ALOAD(rlv,rlv)
      243, // [2][214] - r: FLOAT_LOAD(riv,riv)
      244, // [2][215] - r: FLOAT_LOAD(rlv,rlv)
      247, // [2][216] - r: FLOAT_ALOAD(riv,riv)
      248, // [2][217] - r: FLOAT_ALOAD(rlv,riv)
      249, // [2][218] - r: FLOAT_ALOAD(riv,r)
      250, // [2][219] - r: FLOAT_ALOAD(rlv,rlv)
      371, // [2][220] - r: INT_2FLOAT(riv)
      372, // [2][221] - r: INT_2FLOAT(load32)
      373, // [2][222] - r: INT_2DOUBLE(riv)
      374, // [2][223] - r: INT_2DOUBLE(load32)
      375, // [2][224] - r: FLOAT_2DOUBLE(r)
      376, // [2][225] - r: FLOAT_2DOUBLE(float_load)
      377, // [2][226] - r: DOUBLE_2FLOAT(r)
      378, // [2][227] - r: DOUBLE_2FLOAT(double_load)
      379, // [2][228] - r: FLOAT_2INT(r)
      380, // [2][229] - r: FLOAT_2LONG(r)
      381, // [2][230] - r: DOUBLE_2INT(r)
      382, // [2][231] - r: DOUBLE_2LONG(r)
      383, // [2][232] - r: FLOAT_AS_INT_BITS(r)
      385, // [2][233] - r: DOUBLE_AS_LONG_BITS(r)
      387, // [2][234] - r: INT_BITS_AS_FLOAT(riv)
      389, // [2][235] - r: LONG_BITS_AS_DOUBLE(rlv)
      391, // [2][236] - r: MATERIALIZE_FP_CONSTANT(any)
      465, // [2][237] - r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
      466, // [2][238] - r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
      467, // [2][239] - r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
      468, // [2][240] - r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
      469, // [2][241] - r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
      470, // [2][242] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
      497, // [2][243] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
      498, // [2][244] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
      499, // [2][245] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
      500, // [2][246] - r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
      471, // [2][247] - r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
      472, // [2][248] - r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
      648, // [2][249] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      649, // [2][250] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      652, // [2][251] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      653, // [2][252] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      656, // [2][253] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      657, // [2][254] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      660, // [2][255] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      661, // [2][256] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      650, // [2][257] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      651, // [2][258] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      654, // [2][259] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      655, // [2][260] - r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      658, // [2][261] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      659, // [2][262] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      662, // [2][263] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      663, // [2][264] - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
    },
    { // czr_NT
      0, // [3][0]
      84, // [3][1] - czr: INT_ADD(r,riv)
      86, // [3][2] - czr: INT_ADD(r,load32)
      87, // [3][3] - czr: INT_ADD(load32,riv)
      330, // [3][4] - czr: INT_MOVE(czr)
      124, // [3][5] - czr: INT_SUB(riv,r)
      127, // [3][6] - czr: INT_SUB(riv,load32)
      128, // [3][7] - czr: INT_SUB(load32,riv)
      162, // [3][8] - czr: LONG_ADD(r,rlv)
      163, // [3][9] - czr: LONG_ADD(r,riv)
      164, // [3][10] - czr: LONG_ADD(r,r)
      166, // [3][11] - czr: LONG_ADD(rlv,load64)
      167, // [3][12] - czr: LONG_ADD(load64,rlv)
      201, // [3][13] - czr: LONG_SUB(rlv,r)
      204, // [3][14] - czr: LONG_SUB(rlv,load64)
      205, // [3][15] - czr: LONG_SUB(load64,rlv)
    },
    { // cz_NT
      0, // [4][0]
      3, // [4][1] - cz: czr
      331, // [4][2] - cz: INT_MOVE(cz)
    },
    { // szpr_NT
      0, // [5][0]
      317, // [5][1] - szpr: INT_2USHORT(r)
      88, // [5][2] - szpr: INT_AND(r,riv)
      90, // [5][3] - szpr: INT_AND(r,load32)
      91, // [5][4] - szpr: INT_AND(load32,riv)
      332, // [5][5] - szpr: INT_MOVE(szpr)
      341, // [5][6] - szpr: INT_NEG(r)
      115, // [5][7] - szpr: INT_OR(r,riv)
      116, // [5][8] - szpr: INT_OR(r,load32)
      117, // [5][9] - szpr: INT_OR(load32,riv)
      628, // [5][10] - szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
      122, // [5][11] - szpr: INT_SHL(riv,riv)
      343, // [5][12] - szpr: INT_SHL(r,INT_CONSTANT)
      400, // [5][13] - szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      629, // [5][14] - szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
      123, // [5][15] - szpr: INT_SHR(riv,riv)
      345, // [5][16] - szpr: INT_SHR(riv,INT_CONSTANT)
      631, // [5][17] - szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
      129, // [5][18] - szpr: INT_USHR(riv,riv)
      346, // [5][19] - szpr: INT_USHR(riv,INT_CONSTANT)
      130, // [5][20] - szpr: INT_XOR(r,riv)
      131, // [5][21] - szpr: INT_XOR(r,load32)
      132, // [5][22] - szpr: INT_XOR(load32,riv)
      168, // [5][23] - szpr: LONG_AND(r,rlv)
      169, // [5][24] - szpr: LONG_AND(r,r)
      171, // [5][25] - szpr: LONG_AND(rlv,load64)
      172, // [5][26] - szpr: LONG_AND(load64,rlv)
      357, // [5][27] - szpr: LONG_NEG(r)
      191, // [5][28] - szpr: LONG_OR(r,rlv)
      192, // [5][29] - szpr: LONG_OR(r,load64)
      193, // [5][30] - szpr: LONG_OR(load64,rlv)
      632, // [5][31] - szpr: LONG_SHL(rlv,INT_AND(r,INT_CONSTANT))
      199, // [5][32] - szpr: LONG_SHL(rlv,riv)
      359, // [5][33] - szpr: LONG_SHL(r,INT_CONSTANT)
      407, // [5][34] - szpr: LONG_SHL(LONG_SHR(r,INT_CONSTANT),INT_CONSTANT)
      633, // [5][35] - szpr: LONG_SHR(rlv,INT_AND(r,LONG_CONSTANT))
      200, // [5][36] - szpr: LONG_SHR(rlv,riv)
      361, // [5][37] - szpr: LONG_SHR(rlv,LONG_CONSTANT)
      635, // [5][38] - szpr: LONG_USHR(rlv,LONG_AND(r,LONG_CONSTANT))
      206, // [5][39] - szpr: LONG_USHR(rlv,riv)
      362, // [5][40] - szpr: LONG_USHR(rlv,LONG_CONSTANT)
      207, // [5][41] - szpr: LONG_XOR(r,rlv)
      208, // [5][42] - szpr: LONG_XOR(r,load64)
      209, // [5][43] - szpr: LONG_XOR(load64,rlv)
    },
    { // szp_NT
      0, // [6][0]
      5, // [6][1] - szp: szpr
      89, // [6][2] - szp: INT_AND(r,riv)
      92, // [6][3] - szp: INT_AND(load8_16_32,riv)
      93, // [6][4] - szp: INT_AND(r,load8_16_32)
      333, // [6][5] - szp: INT_MOVE(szp)
      170, // [6][6] - szp: LONG_AND(r,rlv)
      173, // [6][7] - szp: LONG_AND(load8_16_32_64,rlv)
      174, // [6][8] - szp: LONG_AND(r,load8_16_32_64)
    },
    { // riv_NT
      0, // [7][0]
      6, // [7][1] - riv: r
      22, // [7][2] - riv: INT_CONSTANT
    },
    { // rlv_NT
      0, // [8][0]
      7, // [8][1] - rlv: r
      23, // [8][2] - rlv: LONG_CONSTANT
    },
    { // any_NT
      0, // [9][0]
      24, // [9][1] - any: NULL
      8, // [9][2] - any: riv
      25, // [9][3] - any: ADDRESS_CONSTANT
      26, // [9][4] - any: LONG_CONSTANT
      54, // [9][5] - any: OTHER_OPERAND(any,any)
    },
    { // load32_NT
      0, // [10][0]
      340, // [10][1] - load32: INT_MOVE(load32)
      157, // [10][2] - load32: INT_LOAD(rlv,rlv)
      158, // [10][3] - load32: INT_ALOAD(rlv,riv)
      351, // [10][4] - load32: LONG_2INT(load64)
      405, // [10][5] - load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      406, // [10][6] - load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      384, // [10][7] - load32: FLOAT_AS_INT_BITS(float_load)
    },
    { // uload8_NT
      0, // [11][0]
      263, // [11][1] - uload8: INT_AND(load8_16_32,INT_CONSTANT)
      335, // [11][2] - uload8: INT_MOVE(uload8)
      143, // [11][3] - uload8: UBYTE_LOAD(rlv,rlv)
      146, // [11][4] - uload8: UBYTE_ALOAD(rlv,riv)
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
      339, // [14][1] - load16: INT_MOVE(load16)
      13, // [14][2] - load16: sload16
      14, // [14][3] - load16: uload16
    },
    { // address1scaledreg_NT
      0, // [15][0]
      9, // [15][1] - address1scaledreg: address1reg
      269, // [15][2] - address1scaledreg: INT_SHL(r,INT_CONSTANT)
      273, // [15][3] - address1scaledreg: INT_ADD(address1scaledreg,LONG_CONSTANT)
      275, // [15][4] - address1scaledreg: LONG_SHL(r,INT_CONSTANT)
      279, // [15][5] - address1scaledreg: LONG_ADD(address1scaledreg,LONG_CONSTANT)
    },
    { // address1reg_NT
      0, // [16][0]
      270, // [16][1] - address1reg: INT_ADD(r,LONG_CONSTANT)
      271, // [16][2] - address1reg: INT_MOVE(r)
      272, // [16][3] - address1reg: INT_ADD(address1reg,LONG_CONSTANT)
      276, // [16][4] - address1reg: LONG_ADD(r,LONG_CONSTANT)
      277, // [16][5] - address1reg: LONG_MOVE(r)
      278, // [16][6] - address1reg: LONG_ADD(address1reg,LONG_CONSTANT)
    },
    { // address_NT
      0, // [17][0]
      10, // [17][1] - address: address1scaledreg
      62, // [17][2] - address: INT_ADD(r,r)
      63, // [17][3] - address: INT_ADD(r,address1scaledreg)
      64, // [17][4] - address: INT_ADD(address1scaledreg,r)
      274, // [17][5] - address: INT_ADD(address1scaledreg,LONG_CONSTANT)
      65, // [17][6] - address: INT_ADD(address1scaledreg,address1reg)
      66, // [17][7] - address: INT_ADD(address1reg,address1scaledreg)
      67, // [17][8] - address: LONG_ADD(r,r)
      68, // [17][9] - address: LONG_ADD(r,address1scaledreg)
      69, // [17][10] - address: LONG_ADD(address1scaledreg,r)
      280, // [17][11] - address: LONG_ADD(address1scaledreg,LONG_CONSTANT)
      70, // [17][12] - address: LONG_ADD(address1scaledreg,address1reg)
      71, // [17][13] - address: LONG_ADD(address1reg,address1scaledreg)
    },
    { // bittest_NT
      0, // [18][0]
      533, // [18][1] - bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      534, // [18][2] - bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      396, // [18][3] - bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
      535, // [18][4] - bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      536, // [18][5] - bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      397, // [18][6] - bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      537, // [18][7] - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
      538, // [18][8] - bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
      539, // [18][9] - bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      540, // [18][10] - bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
    },
    { // boolcmp_NT
      0, // [19][0]
      73, // [19][1] - boolcmp: BOOLEAN_CMP_INT(r,riv)
      282, // [19][2] - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      288, // [19][3] - boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      290, // [19][4] - boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      292, // [19][5] - boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      294, // [19][6] - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      296, // [19][7] - boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      75, // [19][8] - boolcmp: BOOLEAN_CMP_INT(load32,riv)
      77, // [19][9] - boolcmp: BOOLEAN_CMP_INT(riv,load32)
      79, // [19][10] - boolcmp: BOOLEAN_CMP_LONG(r,rlv)
      298, // [19][11] - boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      81, // [19][12] - boolcmp: BOOLEAN_CMP_LONG(load64,rlv)
      83, // [19][13] - boolcmp: BOOLEAN_CMP_LONG(rlv,load64)
    },
    { // load64_NT
      0, // [20][0]
      159, // [20][1] - load64: LONG_LOAD(rlv,rlv)
      160, // [20][2] - load64: LONG_ALOAD(rlv,rlv)
      161, // [20][3] - load64: LONG_ALOAD(rlv,r)
      356, // [20][4] - load64: LONG_MOVE(load64)
      386, // [20][5] - load64: DOUBLE_AS_LONG_BITS(double_load)
    },
    { // load8_NT
      0, // [21][0]
      336, // [21][1] - load8: INT_MOVE(load8)
      11, // [21][2] - load8: sload8
      12, // [21][3] - load8: uload8
    },
    { // sload16_NT
      0, // [22][0]
      316, // [22][1] - sload16: INT_2SHORT(load16_32)
      337, // [22][2] - sload16: INT_MOVE(sload16)
      148, // [22][3] - sload16: SHORT_LOAD(rlv,rlv)
      151, // [22][4] - sload16: SHORT_ALOAD(rlv,riv)
    },
    { // uload16_NT
      0, // [23][0]
      318, // [23][1] - uload16: INT_2USHORT(load16_32)
      338, // [23][2] - uload16: INT_MOVE(uload16)
      153, // [23][3] - uload16: USHORT_LOAD(rlv,rlv)
      156, // [23][4] - uload16: USHORT_ALOAD(rlv,riv)
    },
    { // sload8_NT
      0, // [24][0]
      334, // [24][1] - sload8: INT_MOVE(sload8)
      138, // [24][2] - sload8: BYTE_LOAD(rlv,rlv)
      141, // [24][3] - sload8: BYTE_ALOAD(rlv,riv)
    },
    { // load8_16_32_64_NT
      0, // [25][0]
      19, // [25][1] - load8_16_32_64: load64
      20, // [25][2] - load8_16_32_64: load8_16_32
    },
    { // float_load_NT
      0, // [26][0]
      245, // [26][1] - float_load: FLOAT_LOAD(riv,riv)
      246, // [26][2] - float_load: FLOAT_ALOAD(rlv,riv)
      251, // [26][3] - float_load: FLOAT_ALOAD(riv,riv)
      388, // [26][4] - float_load: INT_BITS_AS_FLOAT(load32)
      392, // [26][5] - float_load: MATERIALIZE_FP_CONSTANT(any)
    },
    { // double_load_NT
      0, // [27][0]
      235, // [27][1] - double_load: DOUBLE_LOAD(riv,riv)
      238, // [27][2] - double_load: DOUBLE_LOAD(rlv,rlv)
      241, // [27][3] - double_load: DOUBLE_ALOAD(rlv,riv)
      242, // [27][4] - double_load: DOUBLE_ALOAD(riv,riv)
      390, // [27][5] - double_load: LONG_BITS_AS_DOUBLE(load64)
      393, // [27][6] - double_load: MATERIALIZE_FP_CONSTANT(any)
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
      p.writePacked(1, 0xFFFFFF3F, 0x40); // p.rlv = 1
    }
    if(BURS.DEBUG) trace(p, 6, c + 0, p.getCost(7) /* riv */);
    if (c < p.getCost(7) /* riv */) {
      p.setCost(7 /* riv */, (char)(c));
      p.writePacked(1, 0xFFFFFFCF, 0x10); // p.riv = 1
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
      p.writePacked(0, 0xFF9FFFFF, 0x200000); // p.cz = 1
    }
    if(BURS.DEBUG) trace(p, 2, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x200); // p.r = 2
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
      p.writePacked(1, 0xFFFFFFF0, 0x1); // p.szp = 1
    }
    if(BURS.DEBUG) trace(p, 4, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x300); // p.r = 3
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
      p.writePacked(1, 0xFFFFF8FF, 0x200); // p.any = 2
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
      p.writePacked(1, 0xFFE7FFFF, 0x100000); // p.load16_32 = 2
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
    if(BURS.DEBUG) trace(p, 12, c + 0, p.getCost(21) /* load8 */);
    if (c < p.getCost(21) /* load8 */) {
      p.setCost(21 /* load8 */, (char)(c));
      p.writePacked(2, 0xFFFE7FFF, 0x18000); // p.load8 = 3
      closure_load8(p, c);
    }
  }

  /**
   * Create closure for load8_16_32
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_load8_16_32(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 20, c + 0, p.getCost(25) /* load8_16_32_64 */);
    if (c < p.getCost(25) /* load8_16_32_64 */) {
      p.setCost(25 /* load8_16_32_64 */, (char)(c));
      p.writePacked(2, 0xF9FFFFFF, 0x4000000); // p.load8_16_32_64 = 2
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
      p.writePacked(1, 0xFFF9FFFF, 0x20000); // p.load8_16_32 = 1
      closure_load8_16_32(p, c);
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
      p.writePacked(1, 0xFFE7FFFF, 0x80000); // p.load16_32 = 1
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
    if(BURS.DEBUG) trace(p, 10, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x1); // p.address = 1
    }
  }

  /**
   * Create closure for address1reg
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_address1reg(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 9, c + 0, p.getCost(15) /* address1scaledreg */);
    if (c < p.getCost(15) /* address1scaledreg */) {
      p.setCost(15 /* address1scaledreg */, (char)(c));
      p.writePacked(1, 0xFC7FFFFF, 0x800000); // p.address1scaledreg = 1
      closure_address1scaledreg(p, c);
    }
  }

  /**
   * Create closure for load64
   * @param p the node
   * @param c the cost
   */
  @Inline
  private static void closure_load64(AbstractBURS_TreeNode p, int c) {
    if(BURS.DEBUG) trace(p, 19, c + 0, p.getCost(25) /* load8_16_32_64 */);
    if (c < p.getCost(25) /* load8_16_32_64 */) {
      p.setCost(25 /* load8_16_32_64 */, (char)(c));
      p.writePacked(2, 0xF9FFFFFF, 0x2000000); // p.load8_16_32_64 = 1
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
      p.writePacked(1, 0xFFF9FFFF, 0x40000); // p.load8_16_32 = 2
      closure_load8_16_32(p, c);
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
      p.writePacked(1, 0xFF9FFFFF, 0x400000); // p.load16 = 2
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
      p.writePacked(1, 0xFF9FFFFF, 0x600000); // p.load16 = 3
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
    if(BURS.DEBUG) trace(p, 11, c + 0, p.getCost(21) /* load8 */);
    if (c < p.getCost(21) /* load8 */) {
      p.setCost(21 /* load8 */, (char)(c));
      p.writePacked(2, 0xFFFE7FFF, 0x10000); // p.load8 = 2
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
    case LONG_DIV_opcode:
      label_LONG_DIV(p);
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
    case LONG_REM_opcode:
      label_LONG_REM(p);
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
    case INT_2ADDRZerExt_opcode:
      label_INT_2ADDRZerExt(p);
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
    if(BURS.DEBUG) trace(p, 39, 11 + 0, p.getCost(2) /* r */);
    if (11 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(11));
      p.writePacked(0, 0xFFFE00FF, 0x700); // p.r = 7
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
    if(BURS.DEBUG) trace(p, 260, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xD); // p.stm = 13
    }
    if ( // stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = 20;
      if(BURS.DEBUG) trace(p, 40, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xE); // p.stm = 14
      }
    }
    if ( // stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
      lchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = 20;
      if(BURS.DEBUG) trace(p, 41, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 27, 10 + 0, p.getCost(1) /* stm */);
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
    // r: INT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 111, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6400); // p.r = 100
      closure_r(p, c);
    }
    // load32: INT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 158, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFC7FF, 0x1800); // p.load32 = 3
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
    // load64: LONG_ALOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 160, c + 0, p.getCost(20) /* load64 */);
    if (c < p.getCost(20) /* load64 */) {
      p.setCost(20 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x2000); // p.load64 = 2
      closure_load64(p, c);
    }
    // load64: LONG_ALOAD(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 161, c + 0, p.getCost(20) /* load64 */);
    if (c < p.getCost(20) /* load64 */) {
      p.setCost(20 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x3000); // p.load64 = 3
      closure_load64(p, c);
    }
    // r: LONG_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 30;
    if(BURS.DEBUG) trace(p, 186, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA100); // p.r = 161
      closure_r(p, c);
    }
    // r: LONG_ALOAD(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 20;
    if(BURS.DEBUG) trace(p, 187, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA200); // p.r = 162
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
    if(BURS.DEBUG) trace(p, 246, c + 0, p.getCost(26) /* float_load */);
    if (c < p.getCost(26) /* float_load */) {
      p.setCost(26 /* float_load */, (char)(c));
      p.writePacked(2, 0xC7FFFFFF, 0x10000000); // p.float_load = 2
    }
    // r: FLOAT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 247, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD800); // p.r = 216
      closure_r(p, c);
    }
    // r: FLOAT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 248, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD900); // p.r = 217
      closure_r(p, c);
    }
    // r: FLOAT_ALOAD(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 249, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xDA00); // p.r = 218
      closure_r(p, c);
    }
    // r: FLOAT_ALOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 250, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xDB00); // p.r = 219
      closure_r(p, c);
    }
    // float_load: FLOAT_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 251, c + 0, p.getCost(26) /* float_load */);
    if (c < p.getCost(26) /* float_load */) {
      p.setCost(26 /* float_load */, (char)(c));
      p.writePacked(2, 0xC7FFFFFF, 0x18000000); // p.float_load = 3
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
    if(BURS.DEBUG) trace(p, 236, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD200); // p.r = 210
      closure_r(p, c);
    }
    // r: DOUBLE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 237, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD300); // p.r = 211
      closure_r(p, c);
    }
    // r: DOUBLE_ALOAD(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 239, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD400); // p.r = 212
      closure_r(p, c);
    }
    // r: DOUBLE_ALOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 10;
    if(BURS.DEBUG) trace(p, 240, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD500); // p.r = 213
      closure_r(p, c);
    }
    // double_load: DOUBLE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 241, c + 0, p.getCost(27) /* double_load */);
    if (c < p.getCost(27) /* double_load */) {
      p.setCost(27 /* double_load */, (char)(c));
      p.writePacked(3, 0xFFFFFFF8, 0x3); // p.double_load = 3
    }
    // double_load: DOUBLE_ALOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 242, c + 0, p.getCost(27) /* double_load */);
    if (c < p.getCost(27) /* double_load */) {
      p.setCost(27 /* double_load */, (char)(c));
      p.writePacked(3, 0xFFFFFFF8, 0x4); // p.double_load = 4
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
    // r: UBYTE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 144, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8700); // p.r = 135
      closure_r(p, c);
    }
    // r: UBYTE_ALOAD(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 145, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8800); // p.r = 136
      closure_r(p, c);
    }
    // uload8: UBYTE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 146, c + 0, p.getCost(11) /* uload8 */);
    if (c < p.getCost(11) /* uload8 */) {
      p.setCost(11 /* uload8 */, (char)(c));
      p.writePacked(1, 0xFFFE3FFF, 0x10000); // p.uload8 = 4
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
    // r: BYTE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 139, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8400); // p.r = 132
      closure_r(p, c);
    }
    // r: BYTE_ALOAD(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 140, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8500); // p.r = 133
      closure_r(p, c);
    }
    // sload8: BYTE_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 141, c + 0, p.getCost(24) /* sload8 */);
    if (c < p.getCost(24) /* sload8 */) {
      p.setCost(24 /* sload8 */, (char)(c));
      p.writePacked(2, 0xFE7FFFFF, 0x1800000); // p.sload8 = 3
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
    // r: USHORT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 154, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8D00); // p.r = 141
      closure_r(p, c);
    }
    // r: USHORT_ALOAD(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 155, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8E00); // p.r = 142
      closure_r(p, c);
    }
    // uload16: USHORT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 156, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x400000); // p.uload16 = 4
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
    // r: SHORT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 20;
    if(BURS.DEBUG) trace(p, 149, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8A00); // p.r = 138
      closure_r(p, c);
    }
    // r: SHORT_ALOAD(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 150, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8B00); // p.r = 139
      closure_r(p, c);
    }
    // sload16: SHORT_ALOAD(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 151, c + 0, p.getCost(22) /* sload16 */);
    if (c < p.getCost(22) /* sload16 */) {
      p.setCost(22 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x80000); // p.sload16 = 4
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
      if(BURS.DEBUG) trace(p, 415, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1D); // p.stm = 29
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 416, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1E); // p.stm = 30
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 417, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1F); // p.stm = 31
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 418, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x20); // p.stm = 32
      }
    }
    if ( // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 419, c + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 581, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5F); // p.stm = 95
      }
    }
    if ( // stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_ADD_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 601, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x60); // p.stm = 96
      }
    }
    if ( // stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 583, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x63); // p.stm = 99
      }
    }
    if ( // stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 603, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x64); // p.stm = 100
      }
    }
    if ( // stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NEG_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 544, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x76); // p.stm = 118
      }
    }
    if ( // stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NOT_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 546, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x78); // p.stm = 120
      }
    }
    if ( // stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 585, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7B); // p.stm = 123
      }
    }
    if ( // stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 605, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7C); // p.stm = 124
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
      if(BURS.DEBUG) trace(p, 637, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7F); // p.stm = 127
      }
    }
    if ( // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 31 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 548, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x80); // p.stm = 128
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
      if(BURS.DEBUG) trace(p, 639, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x83); // p.stm = 131
      }
    }
    if ( // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 31 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 550, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x84); // p.stm = 132
      }
    }
    if ( // stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 587, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8D); // p.stm = 141
      }
    }
    if ( // stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 27);
      if(BURS.DEBUG) trace(p, 607, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8E); // p.stm = 142
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
      if(BURS.DEBUG) trace(p, 641, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x91); // p.stm = 145
      }
    }
    if ( // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 31 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 552, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x92); // p.stm = 146
      }
    }
    if ( // stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild1().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 589, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x95); // p.stm = 149
      }
    }
    if ( // stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild2().getOpcode() == INT_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 609, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x96); // p.stm = 150
      }
    }
    if ( // stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_2INT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 579, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x98); // p.stm = 152
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
      if(BURS.DEBUG) trace(p, 420, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x22); // p.stm = 34
      }
    }
    if ( // stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 421, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x23); // p.stm = 35
      }
    }
    if ( // stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 422, c + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 477, c + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 478, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 591, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9B); // p.stm = 155
      }
    }
    if ( // stm: LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_ADD_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 611, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9C); // p.stm = 156
      }
    }
    if ( // stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 593, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9F); // p.stm = 159
      }
    }
    if ( // stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 613, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA0); // p.stm = 160
      }
    }
    if ( // stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NEG_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 554, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA4); // p.stm = 164
      }
    }
    if ( // stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NOT_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 556, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA6); // p.stm = 166
      }
    }
    if ( // stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 595, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA9); // p.stm = 169
      }
    }
    if ( // stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 615, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAA); // p.stm = 170
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHL_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 63 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 643, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAD); // p.stm = 173
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHL_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 63 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 558, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAE); // p.stm = 174
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 63 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 645, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB1); // p.stm = 177
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 63 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 560, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB2); // p.stm = 178
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_SUB_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 597, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBB); // p.stm = 187
      }
    }
    if ( // stm: LONG_ASTORE(LONG_SUB(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_SUB_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 27);
      if(BURS.DEBUG) trace(p, 617, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBC); // p.stm = 188
      }
    }
    if ( // stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 63 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 647, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBF); // p.stm = 191
      }
    }
    if ( // stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      lchild.getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ARRAY_ADDRESS_EQUAL(P(p), PLL(p), VLR(p) == 63 ? 17 : INFINITE));
      if(BURS.DEBUG) trace(p, 562, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC0); // p.stm = 192
      }
    }
    if ( // stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild1().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 599, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC3); // p.stm = 195
      }
    }
    if ( // stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild2().getOpcode() == LONG_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ARRAY_ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 619, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC4); // p.stm = 196
      }
    }
    if ( // stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 473, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xDE); // p.stm = 222
      }
    }
    if ( // stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 474, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xDF); // p.stm = 223
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
      if(BURS.DEBUG) trace(p, 460, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD2); // p.stm = 210
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 461, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD3); // p.stm = 211
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 462, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD4); // p.stm = 212
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 463, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD5); // p.stm = 213
      }
    }
    if ( // stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 12;
      if(BURS.DEBUG) trace(p, 464, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD6); // p.stm = 214
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
      if(BURS.DEBUG) trace(p, 451, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC9); // p.stm = 201
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 452, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xCA); // p.stm = 202
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 453, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xCB); // p.stm = 203
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 454, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xCC); // p.stm = 204
      }
    }
    if ( // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 12;
      if(BURS.DEBUG) trace(p, 455, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xCD); // p.stm = 205
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
      if(BURS.DEBUG) trace(p, 424, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x50); // p.stm = 80
      }
    }
    if ( // stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv,riv))
      lchild.getOpcode() == BOOLEAN_NOT_opcode && 
      lchild.getChild1().getOpcode() == UBYTE_ALOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ARRAY_ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 542, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x52); // p.stm = 82
      }
    }
    if ( // stm: BYTE_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 427, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x55); // p.stm = 85
      }
    }
    if ( // stm: BYTE_ASTORE(load8,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(21 /* load8 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 428, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x56); // p.stm = 86
      }
    }
    if ( // stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2BYTE_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 573, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x58); // p.stm = 88
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
      if(BURS.DEBUG) trace(p, 412, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1A); // p.stm = 26
      }
    }
    if ( // stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(14 /* load16 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 413, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x1B); // p.stm = 27
      }
    }
    if ( // stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 414, c + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 575, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5A); // p.stm = 90
      }
    }
    if ( // stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2USHORT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 577, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5C); // p.stm = 92
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
      if(BURS.DEBUG) trace(p, 505, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 506, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 507, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 508, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 509, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 525, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild2().getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 529, c + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 510, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 511, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 512, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 513, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 514, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 526, c + 0, p.getCost(1) /* stm */);
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
      c = STATE(lchild.getChild2().getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(7 /* riv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 530, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x40); // p.stm = 64
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 515, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x41); // p.stm = 65
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 516, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x42); // p.stm = 66
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 517, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x43); // p.stm = 67
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 518, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x44); // p.stm = 68
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 519, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x45); // p.stm = 69
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p), 54);
      if(BURS.DEBUG) trace(p, 527, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x46); // p.stm = 70
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isZERO(VR(p),54);
      if(BURS.DEBUG) trace(p, 531, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x47); // p.stm = 71
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 520, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x48); // p.stm = 72
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 521, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x49); // p.stm = 73
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 522, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4A); // p.stm = 74
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 523, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4B); // p.stm = 75
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(16 /* address1reg */) + STATE(lchild.getChild2().getChild1()).getCost(15 /* address1scaledreg */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 524, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4C); // p.stm = 76
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 528, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4D); // p.stm = 77
      }
    }
    if ( // stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      lchild.getOpcode() == ATTEMPT_LONG_opcode && 
      lchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(17 /* address */) + STATE(lchild.getChild2().getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2().getChild2()).getCost(8 /* rlv */) + isONE(VR(p), 54);
      if(BURS.DEBUG) trace(p, 532, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4E); // p.stm = 78
      }
    }
    // stm: INT_IFCMP(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 26;
    if(BURS.DEBUG) trace(p, 98, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x65); // p.stm = 101
    }
    if ( // stm: INT_IFCMP(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && CMP_TO_TEST(IfCmp.getCond(P(p))) ? 24:INFINITE);
      if(BURS.DEBUG) trace(p, 320, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x66); // p.stm = 102
      }
    }
    if ( // stm: INT_IFCMP(load8,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(21 /* load8 */) + FITS(IfCmp.getVal2(P(p)), 8, 28);
      if(BURS.DEBUG) trace(p, 321, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x67); // p.stm = 103
      }
    }
    // stm: INT_IFCMP(uload8,r)
    c = STATE(lchild).getCost(11 /* uload8 */) + STATE(rchild).getCost(2 /* r */) + 28;
    if(BURS.DEBUG) trace(p, 99, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x68); // p.stm = 104
    }
    // stm: INT_IFCMP(r,uload8)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(11 /* uload8 */) + 28;
    if(BURS.DEBUG) trace(p, 100, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x69); // p.stm = 105
    }
    if ( // stm: INT_IFCMP(sload16,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(22 /* sload16 */) + FITS(IfCmp.getVal2(P(p)), 8, 28);
      if(BURS.DEBUG) trace(p, 322, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6A); // p.stm = 106
      }
    }
    // stm: INT_IFCMP(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 28;
    if(BURS.DEBUG) trace(p, 101, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x6B); // p.stm = 107
    }
    // stm: INT_IFCMP(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 28;
    if(BURS.DEBUG) trace(p, 102, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x6C); // p.stm = 108
    }
    if ( // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && IfCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 1 && IfCmp.getCond(P(p)).isEQUAL()) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 323, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6D); // p.stm = 109
      }
    }
    if ( // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && IfCmp.getCond(P(p)).isEQUAL()) || (VR(p) == 1 && IfCmp.getCond(P(p)).isNOT_EQUAL()) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 324, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6E); // p.stm = 110
      }
    }
    if ( // stm: INT_IFCMP(cz,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + isZERO(VR(p), 11);
      if(BURS.DEBUG) trace(p, 325, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x6F); // p.stm = 111
      }
    }
    if ( // stm: INT_IFCMP(szp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + (VR(p) == 0 && EQ_NE(IfCmp.getCond(P(p)))?11:INFINITE);
      if(BURS.DEBUG) trace(p, 326, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x70); // p.stm = 112
      }
    }
    if ( // stm: INT_IFCMP(bittest,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + ((VR(p) == 0 || VR(p) == 1) && EQ_NE(IfCmp.getCond(P(p))) ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 327, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x71); // p.stm = 113
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
    if(BURS.DEBUG) trace(p, 103, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x72); // p.stm = 114
    }
    // stm: INT_IFCMP2(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 28;
    if(BURS.DEBUG) trace(p, 104, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x73); // p.stm = 115
    }
    // stm: INT_IFCMP2(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 28;
    if(BURS.DEBUG) trace(p, 105, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x74); // p.stm = 116
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
    // stm: LONG_IFCMP(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 26;
    if(BURS.DEBUG) trace(p, 180, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xA1); // p.stm = 161
    }
    if ( // stm: LONG_IFCMP(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (LV(IfCmp.getVal2(P(p))) == 0 && CMP_TO_TEST(IfCmp.getCond(P(p))) ? 24:INFINITE);
      if(BURS.DEBUG) trace(p, 352, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA2); // p.stm = 162
      }
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
    if(BURS.DEBUG) trace(p, 252, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xD8); // p.stm = 216
    }
    // stm: FLOAT_IFCMP(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 253, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xD9); // p.stm = 217
    }
    // stm: FLOAT_IFCMP(float_load,r)
    c = STATE(lchild).getCost(26 /* float_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 254, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xDA); // p.stm = 218
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
    if(BURS.DEBUG) trace(p, 255, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xDB); // p.stm = 219
    }
    // stm: DOUBLE_IFCMP(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(27 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 256, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xDC); // p.stm = 220
    }
    // stm: DOUBLE_IFCMP(double_load,r)
    c = STATE(lchild).getCost(27 /* double_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 257, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0xDD); // p.stm = 221
    }
  }

  /**
   * Labels UNINT_BEGIN tree node
   * @param p node to label
   */
  private static void label_UNINT_BEGIN(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: UNINT_BEGIN
    if(BURS.DEBUG) trace(p, 28, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 29, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 46, 11 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 45, 11 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 44, 11 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 35, 10 + 0, p.getCost(1) /* stm */);
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
    // address1reg: INT_MOVE(r)
    c = STATE(lchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 271, c + 0, p.getCost(16) /* address1reg */);
    if (c < p.getCost(16) /* address1reg */) {
      p.setCost(16 /* address1reg */, (char)(c));
      p.writePacked(1, 0xE3FFFFFF, 0x8000000); // p.address1reg = 2
      closure_address1reg(p, c);
    }
    // r: INT_MOVE(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 329, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6500); // p.r = 101
      closure_r(p, c);
    }
    // czr: INT_MOVE(czr)
    c = STATE(lchild).getCost(3 /* czr */) + 11;
    if(BURS.DEBUG) trace(p, 330, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x80000); // p.czr = 4
      closure_czr(p, c);
    }
    // cz: INT_MOVE(cz)
    c = STATE(lchild).getCost(4 /* cz */) + 0;
    if(BURS.DEBUG) trace(p, 331, c + 0, p.getCost(4) /* cz */);
    if (c < p.getCost(4) /* cz */) {
      p.setCost(4 /* cz */, (char)(c));
      p.writePacked(0, 0xFF9FFFFF, 0x400000); // p.cz = 2
    }
    // szpr: INT_MOVE(szpr)
    c = STATE(lchild).getCost(5 /* szpr */) + 11;
    if(BURS.DEBUG) trace(p, 332, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x2800000); // p.szpr = 5
      closure_szpr(p, c);
    }
    // szp: INT_MOVE(szp)
    c = STATE(lchild).getCost(6 /* szp */) + 0;
    if(BURS.DEBUG) trace(p, 333, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x5); // p.szp = 5
    }
    // sload8: INT_MOVE(sload8)
    c = STATE(lchild).getCost(24 /* sload8 */) + 0;
    if(BURS.DEBUG) trace(p, 334, c + 0, p.getCost(24) /* sload8 */);
    if (c < p.getCost(24) /* sload8 */) {
      p.setCost(24 /* sload8 */, (char)(c));
      p.writePacked(2, 0xFE7FFFFF, 0x800000); // p.sload8 = 1
      closure_sload8(p, c);
    }
    // uload8: INT_MOVE(uload8)
    c = STATE(lchild).getCost(11 /* uload8 */) + 0;
    if(BURS.DEBUG) trace(p, 335, c + 0, p.getCost(11) /* uload8 */);
    if (c < p.getCost(11) /* uload8 */) {
      p.setCost(11 /* uload8 */, (char)(c));
      p.writePacked(1, 0xFFFE3FFF, 0x8000); // p.uload8 = 2
      closure_uload8(p, c);
    }
    // load8: INT_MOVE(load8)
    c = STATE(lchild).getCost(21 /* load8 */) + 0;
    if(BURS.DEBUG) trace(p, 336, c + 0, p.getCost(21) /* load8 */);
    if (c < p.getCost(21) /* load8 */) {
      p.setCost(21 /* load8 */, (char)(c));
      p.writePacked(2, 0xFFFE7FFF, 0x8000); // p.load8 = 1
      closure_load8(p, c);
    }
    // sload16: INT_MOVE(sload16)
    c = STATE(lchild).getCost(22 /* sload16 */) + 0;
    if(BURS.DEBUG) trace(p, 337, c + 0, p.getCost(22) /* sload16 */);
    if (c < p.getCost(22) /* sload16 */) {
      p.setCost(22 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x40000); // p.sload16 = 2
      closure_sload16(p, c);
    }
    // uload16: INT_MOVE(uload16)
    c = STATE(lchild).getCost(23 /* uload16 */) + 0;
    if(BURS.DEBUG) trace(p, 338, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x200000); // p.uload16 = 2
      closure_uload16(p, c);
    }
    // load16: INT_MOVE(load16)
    c = STATE(lchild).getCost(14 /* load16 */) + 0;
    if(BURS.DEBUG) trace(p, 339, c + 0, p.getCost(14) /* load16 */);
    if (c < p.getCost(14) /* load16 */) {
      p.setCost(14 /* load16 */, (char)(c));
      p.writePacked(1, 0xFF9FFFFF, 0x200000); // p.load16 = 1
      closure_load16(p, c);
    }
    // load32: INT_MOVE(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 0;
    if(BURS.DEBUG) trace(p, 340, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFC7FF, 0x800); // p.load32 = 1
      closure_load32(p, c);
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
    // address1reg: LONG_MOVE(r)
    c = STATE(lchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 277, c + 0, p.getCost(16) /* address1reg */);
    if (c < p.getCost(16) /* address1reg */) {
      p.setCost(16 /* address1reg */, (char)(c));
      p.writePacked(1, 0xE3FFFFFF, 0x14000000); // p.address1reg = 5
      closure_address1reg(p, c);
    }
    // r: LONG_MOVE(address)
    c = STATE(lchild).getCost(17 /* address */) + 20;
    if(BURS.DEBUG) trace(p, 348, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8200); // p.r = 130
      closure_r(p, c);
    }
    // r: LONG_MOVE(rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 354, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA300); // p.r = 163
      closure_r(p, c);
    }
    // r: LONG_MOVE(riv)
    c = STATE(lchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 355, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA400); // p.r = 164
      closure_r(p, c);
    }
    // load64: LONG_MOVE(load64)
    c = STATE(lchild).getCost(20 /* load64 */) + 0;
    if(BURS.DEBUG) trace(p, 356, c + 0, p.getCost(20) /* load64 */);
    if (c < p.getCost(20) /* load64 */) {
      p.setCost(20 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x4000); // p.load64 = 4
      closure_load64(p, c);
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
    if(BURS.DEBUG) trace(p, 369, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xCD00); // p.r = 205
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
    if(BURS.DEBUG) trace(p, 370, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xCE00); // p.r = 206
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
    if(BURS.DEBUG) trace(p, 36, 11 + 0, p.getCost(2) /* r */);
    if (11 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(11));
      p.writePacked(0, 0xFFFE00FF, 0x500); // p.r = 5
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
    if(BURS.DEBUG) trace(p, 37, 11 + 0, p.getCost(2) /* r */);
    if (11 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(11));
      p.writePacked(0, 0xFFFE00FF, 0x600); // p.r = 6
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
    if ( // address1reg: INT_ADD(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 0;
      if(BURS.DEBUG) trace(p, 270, c + 0, p.getCost(16) /* address1reg */);
      if (c < p.getCost(16) /* address1reg */) {
        p.setCost(16 /* address1reg */, (char)(c));
        p.writePacked(1, 0xE3FFFFFF, 0x4000000); // p.address1reg = 1
        closure_address1reg(p, c);
      }
    }
    // address: INT_ADD(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 62, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x2); // p.address = 2
    }
    if ( // address1reg: INT_ADD(address1reg,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1reg */) + 0;
      if(BURS.DEBUG) trace(p, 272, c + 0, p.getCost(16) /* address1reg */);
      if (c < p.getCost(16) /* address1reg */) {
        p.setCost(16 /* address1reg */, (char)(c));
        p.writePacked(1, 0xE3FFFFFF, 0xC000000); // p.address1reg = 3
        closure_address1reg(p, c);
      }
    }
    if ( // address1scaledreg: INT_ADD(address1scaledreg,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + 0;
      if(BURS.DEBUG) trace(p, 273, c + 0, p.getCost(15) /* address1scaledreg */);
      if (c < p.getCost(15) /* address1scaledreg */) {
        p.setCost(15 /* address1scaledreg */, (char)(c));
        p.writePacked(1, 0xFC7FFFFF, 0x1800000); // p.address1scaledreg = 3
        closure_address1scaledreg(p, c);
      }
    }
    // address: INT_ADD(r,address1scaledreg)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 63, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x3); // p.address = 3
    }
    // address: INT_ADD(address1scaledreg,r)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 64, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x4); // p.address = 4
    }
    if ( // address: INT_ADD(address1scaledreg,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + 0;
      if(BURS.DEBUG) trace(p, 274, c + 0, p.getCost(17) /* address */);
      if (c < p.getCost(17) /* address */) {
        p.setCost(17 /* address */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0x5); // p.address = 5
      }
    }
    // address: INT_ADD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(16 /* address1reg */) + 0;
    if(BURS.DEBUG) trace(p, 65, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x6); // p.address = 6
    }
    // address: INT_ADD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 66, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x7); // p.address = 7
    }
    // czr: INT_ADD(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 84, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x20000); // p.czr = 1
      closure_czr(p, c);
    }
    // r: INT_ADD(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 85, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5900); // p.r = 89
      closure_r(p, c);
    }
    // czr: INT_ADD(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 86, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x40000); // p.czr = 2
      closure_czr(p, c);
    }
    // czr: INT_ADD(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 87, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x60000); // p.czr = 3
      closure_czr(p, c);
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
    if ( // address1reg: LONG_ADD(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 0;
      if(BURS.DEBUG) trace(p, 276, c + 0, p.getCost(16) /* address1reg */);
      if (c < p.getCost(16) /* address1reg */) {
        p.setCost(16 /* address1reg */, (char)(c));
        p.writePacked(1, 0xE3FFFFFF, 0x10000000); // p.address1reg = 4
        closure_address1reg(p, c);
      }
    }
    // address: LONG_ADD(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 67, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x8); // p.address = 8
    }
    if ( // address1reg: LONG_ADD(address1reg,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1reg */) + 0;
      if(BURS.DEBUG) trace(p, 278, c + 0, p.getCost(16) /* address1reg */);
      if (c < p.getCost(16) /* address1reg */) {
        p.setCost(16 /* address1reg */, (char)(c));
        p.writePacked(1, 0xE3FFFFFF, 0x18000000); // p.address1reg = 6
        closure_address1reg(p, c);
      }
    }
    if ( // address1scaledreg: LONG_ADD(address1scaledreg,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + 0;
      if(BURS.DEBUG) trace(p, 279, c + 0, p.getCost(15) /* address1scaledreg */);
      if (c < p.getCost(15) /* address1scaledreg */) {
        p.setCost(15 /* address1scaledreg */, (char)(c));
        p.writePacked(1, 0xFC7FFFFF, 0x2800000); // p.address1scaledreg = 5
        closure_address1scaledreg(p, c);
      }
    }
    // address: LONG_ADD(r,address1scaledreg)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 68, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0x9); // p.address = 9
    }
    // address: LONG_ADD(address1scaledreg,r)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(2 /* r */) + 0;
    if(BURS.DEBUG) trace(p, 69, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0xA); // p.address = 10
    }
    if ( // address: LONG_ADD(address1scaledreg,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + 0;
      if(BURS.DEBUG) trace(p, 280, c + 0, p.getCost(17) /* address */);
      if (c < p.getCost(17) /* address */) {
        p.setCost(17 /* address */, (char)(c));
        p.writePacked(2, 0xFFFFFFF0, 0xB); // p.address = 11
      }
    }
    // address: LONG_ADD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(16 /* address1reg */) + 0;
    if(BURS.DEBUG) trace(p, 70, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0xC); // p.address = 12
    }
    // address: LONG_ADD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 0;
    if(BURS.DEBUG) trace(p, 71, c + 0, p.getCost(17) /* address */);
    if (c < p.getCost(17) /* address */) {
      p.setCost(17 /* address */, (char)(c));
      p.writePacked(2, 0xFFFFFFF0, 0xD); // p.address = 13
    }
    // r: LONG_ADD(address1scaledreg,r)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(2 /* r */) + 11;
    if(BURS.DEBUG) trace(p, 133, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x7D00); // p.r = 125
      closure_r(p, c);
    }
    // r: LONG_ADD(r,address1scaledreg)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 11;
    if(BURS.DEBUG) trace(p, 134, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x7E00); // p.r = 126
      closure_r(p, c);
    }
    // r: LONG_ADD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(16 /* address1reg */) + 11;
    if(BURS.DEBUG) trace(p, 135, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x7F00); // p.r = 127
      closure_r(p, c);
    }
    // r: LONG_ADD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 11;
    if(BURS.DEBUG) trace(p, 136, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8000); // p.r = 128
      closure_r(p, c);
    }
    if ( // r: LONG_ADD(address,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address */) + 11;
      if(BURS.DEBUG) trace(p, 347, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x8100); // p.r = 129
        closure_r(p, c);
      }
    }
    // czr: LONG_ADD(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 11;
    if(BURS.DEBUG) trace(p, 162, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x100000); // p.czr = 8
      closure_czr(p, c);
    }
    // czr: LONG_ADD(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 163, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x120000); // p.czr = 9
      closure_czr(p, c);
    }
    // czr: LONG_ADD(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 9;
    if(BURS.DEBUG) trace(p, 164, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x140000); // p.czr = 10
      closure_czr(p, c);
    }
    // r: LONG_ADD(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 165, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9500); // p.r = 149
      closure_r(p, c);
    }
    // czr: LONG_ADD(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 166, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x160000); // p.czr = 11
      closure_czr(p, c);
    }
    // czr: LONG_ADD(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 167, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x180000); // p.czr = 12
      closure_czr(p, c);
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
    if(BURS.DEBUG) trace(p, 210, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB100); // p.r = 177
      closure_r(p, c);
    }
    // r: FLOAT_ADD(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 211, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB200); // p.r = 178
      closure_r(p, c);
    }
    // r: FLOAT_ADD(float_load,r)
    c = STATE(lchild).getCost(26 /* float_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 212, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB300); // p.r = 179
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
    if(BURS.DEBUG) trace(p, 213, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB400); // p.r = 180
      closure_r(p, c);
    }
    // r: DOUBLE_ADD(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(27 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 214, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB500); // p.r = 181
      closure_r(p, c);
    }
    // r: DOUBLE_ADD(double_load,r)
    c = STATE(lchild).getCost(27 /* double_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 215, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB600); // p.r = 182
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
    if(BURS.DEBUG) trace(p, 124, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0xA0000); // p.czr = 5
      closure_czr(p, c);
    }
    // r: INT_SUB(riv,r)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + (Binary.getResult(P(p)).similar(Binary.getVal2(P(p))) ? 13-2 : INFINITE);
    if(BURS.DEBUG) trace(p, 125, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x7700); // p.r = 119
      closure_r(p, c);
    }
    // r: INT_SUB(load32,r)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(2 /* r */) + (Binary.getResult(P(p)).similar(Binary.getVal2(P(p))) ? 15-2 : INFINITE);
    if(BURS.DEBUG) trace(p, 126, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x7800); // p.r = 120
      closure_r(p, c);
    }
    // czr: INT_SUB(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 127, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0xC0000); // p.czr = 6
      closure_czr(p, c);
    }
    // czr: INT_SUB(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 128, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0xE0000); // p.czr = 7
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
    // czr: LONG_SUB(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 201, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x1A0000); // p.czr = 13
      closure_czr(p, c);
    }
    // r: LONG_SUB(rlv,r)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(2 /* r */) + (Binary.getResult(P(p)).similar(Binary.getVal2(P(p))) ? 13-2 : INFINITE);
    if(BURS.DEBUG) trace(p, 202, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xAF00); // p.r = 175
      closure_r(p, c);
    }
    // r: LONG_SUB(load64,r)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(2 /* r */) + (Binary.getResult(P(p)).similar(Binary.getVal2(P(p))) ? 15-2 : INFINITE);
    if(BURS.DEBUG) trace(p, 203, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB000); // p.r = 176
      closure_r(p, c);
    }
    // czr: LONG_SUB(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 204, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x1C0000); // p.czr = 14
      closure_czr(p, c);
    }
    // czr: LONG_SUB(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 205, c + 0, p.getCost(3) /* czr */);
    if (c < p.getCost(3) /* czr */) {
      p.setCost(3 /* czr */, (char)(c));
      p.writePacked(0, 0xFFE1FFFF, 0x1E0000); // p.czr = 15
      closure_czr(p, c);
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
    if(BURS.DEBUG) trace(p, 216, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB700); // p.r = 183
      closure_r(p, c);
    }
    // r: FLOAT_SUB(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 217, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB800); // p.r = 184
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
    if(BURS.DEBUG) trace(p, 218, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xB900); // p.r = 185
      closure_r(p, c);
    }
    // r: DOUBLE_SUB(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(27 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 219, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xBA00); // p.r = 186
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
    if(BURS.DEBUG) trace(p, 112, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6600); // p.r = 102
      closure_r(p, c);
    }
    // r: INT_MUL(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 113, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6700); // p.r = 103
      closure_r(p, c);
    }
    // r: INT_MUL(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 114, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6800); // p.r = 104
      closure_r(p, c);
    }
    // r: INT_MUL(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 189, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA600); // p.r = 166
      closure_r(p, c);
    }
    // r: INT_MUL(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 190, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA700); // p.r = 167
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
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 188, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA500); // p.r = 165
      closure_r(p, c);
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
    if(BURS.DEBUG) trace(p, 220, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xBB00); // p.r = 187
      closure_r(p, c);
    }
    // r: FLOAT_MUL(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 221, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xBC00); // p.r = 188
      closure_r(p, c);
    }
    // r: FLOAT_MUL(float_load,r)
    c = STATE(lchild).getCost(26 /* float_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 222, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xBD00); // p.r = 189
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
    if(BURS.DEBUG) trace(p, 223, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xBE00); // p.r = 190
      closure_r(p, c);
    }
    // r: DOUBLE_MUL(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(27 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 224, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xBF00); // p.r = 191
      closure_r(p, c);
    }
    // r: DOUBLE_MUL(double_load,r)
    c = STATE(lchild).getCost(27 /* double_load */) + STATE(rchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 225, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC000); // p.r = 192
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
    if(BURS.DEBUG) trace(p, 94, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5A00); // p.r = 90
      closure_r(p, c);
    }
    // r: INT_DIV(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 95, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5B00); // p.r = 91
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_DIV tree node
   * @param p node to label
   */
  private static void label_LONG_DIV(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_DIV(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 52;
    if(BURS.DEBUG) trace(p, 175, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9600); // p.r = 150
      closure_r(p, c);
    }
    // r: LONG_DIV(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 52;
    if(BURS.DEBUG) trace(p, 176, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9700); // p.r = 151
      closure_r(p, c);
    }
    // r: LONG_DIV(riv,rlv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(8 /* rlv */) + 52;
    if(BURS.DEBUG) trace(p, 177, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9800); // p.r = 152
      closure_r(p, c);
    }
    // r: LONG_DIV(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(20 /* load64 */) + 55;
    if(BURS.DEBUG) trace(p, 178, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9900); // p.r = 153
      closure_r(p, c);
    }
    // r: LONG_DIV(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 55;
    if(BURS.DEBUG) trace(p, 179, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9A00); // p.r = 154
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
    if(BURS.DEBUG) trace(p, 96, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5C00); // p.r = 92
      closure_r(p, c);
    }
    // r: UNSIGNED_DIV_64_32(rlv,load32)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 97, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5D00); // p.r = 93
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
    if(BURS.DEBUG) trace(p, 120, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6C00); // p.r = 108
      closure_r(p, c);
    }
    // r: UNSIGNED_REM_64_32(rlv,load32)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 121, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6D00); // p.r = 109
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
    if(BURS.DEBUG) trace(p, 226, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC100); // p.r = 193
      closure_r(p, c);
    }
    // r: FLOAT_DIV(r,float_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(26 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 227, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC200); // p.r = 194
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
    if(BURS.DEBUG) trace(p, 228, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC300); // p.r = 195
      closure_r(p, c);
    }
    // r: DOUBLE_DIV(r,double_load)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(27 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 229, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC400); // p.r = 196
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
    if(BURS.DEBUG) trace(p, 118, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6A00); // p.r = 106
      closure_r(p, c);
    }
    // r: INT_REM(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 55;
    if(BURS.DEBUG) trace(p, 119, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6B00); // p.r = 107
      closure_r(p, c);
    }
  }

  /**
   * Labels LONG_REM tree node
   * @param p node to label
   */
  private static void label_LONG_REM(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild, rchild;
    lchild = p.getChild1();
    rchild = p.getChild2();
    label(lchild);
    label(rchild);
    int c;
    // r: LONG_REM(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 52;
    if(BURS.DEBUG) trace(p, 194, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA900); // p.r = 169
      closure_r(p, c);
    }
    // r: LONG_REM(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 52;
    if(BURS.DEBUG) trace(p, 195, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xAA00); // p.r = 170
      closure_r(p, c);
    }
    // r: LONG_REM(riv,rlv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(8 /* rlv */) + 52;
    if(BURS.DEBUG) trace(p, 196, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xAB00); // p.r = 171
      closure_r(p, c);
    }
    // r: LONG_REM(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(20 /* load64 */) + 55;
    if(BURS.DEBUG) trace(p, 197, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xAC00); // p.r = 172
      closure_r(p, c);
    }
    // r: LONG_REM(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 55;
    if(BURS.DEBUG) trace(p, 198, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xAD00); // p.r = 173
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
    if(BURS.DEBUG) trace(p, 230, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC900); // p.r = 201
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
    if(BURS.DEBUG) trace(p, 231, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xCA00); // p.r = 202
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
    if(BURS.DEBUG) trace(p, 341, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x3000000); // p.szpr = 6
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
    // szpr: LONG_NEG(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 357, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xD800000); // p.szpr = 27
      closure_szpr(p, c);
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
    if(BURS.DEBUG) trace(p, 363, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC500); // p.r = 197
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
    if(BURS.DEBUG) trace(p, 364, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC600); // p.r = 198
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
    if(BURS.DEBUG) trace(p, 365, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC700); // p.r = 199
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
    if(BURS.DEBUG) trace(p, 366, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xC800); // p.r = 200
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
      if(BURS.DEBUG) trace(p, 269, c + 0, p.getCost(15) /* address1scaledreg */);
      if (c < p.getCost(15) /* address1scaledreg */) {
        p.setCost(15 /* address1scaledreg */, (char)(c));
        p.writePacked(1, 0xFC7FFFFF, 0x1000000); // p.address1scaledreg = 2
        closure_address1scaledreg(p, c);
      }
    }
    if ( // szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 31 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 628, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x5000000); // p.szpr = 10
        closure_szpr(p, c);
      }
    }
    // szpr: INT_SHL(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 122, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x5800000); // p.szpr = 11
      closure_szpr(p, c);
    }
    if ( // szpr: INT_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 13;
      if(BURS.DEBUG) trace(p, 343, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x6000000); // p.szpr = 12
        closure_szpr(p, c);
      }
    }
    if ( // r: INT_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (!Binary.getResult(P(p)).similar(Binary.getVal1(P(p))) && (Binary.getVal2(P(p)).asIntConstant().value & 0x1f) <= 3 ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 344, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7600); // p.r = 118
        closure_r(p, c);
      }
    }
    if ( // szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((VR(p) == VLR(p)) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 400, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x6800000); // p.szpr = 13
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
    if ( // address1scaledreg: LONG_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + LEA_SHIFT(Binary.getVal2(P(p)), 0);
      if(BURS.DEBUG) trace(p, 275, c + 0, p.getCost(15) /* address1scaledreg */);
      if (c < p.getCost(15) /* address1scaledreg */) {
        p.setCost(15 /* address1scaledreg */, (char)(c));
        p.writePacked(1, 0xFC7FFFFF, 0x2000000); // p.address1scaledreg = 4
        closure_address1scaledreg(p, c);
      }
    }
    if ( // szpr: LONG_SHL(rlv,INT_AND(r,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 63 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 632, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0xF800000); // p.szpr = 31
        closure_szpr(p, c);
      }
    }
    // szpr: LONG_SHL(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 199, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x10000000); // p.szpr = 32
      closure_szpr(p, c);
    }
    if ( // szpr: LONG_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 13;
      if(BURS.DEBUG) trace(p, 359, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x10800000); // p.szpr = 33
        closure_szpr(p, c);
      }
    }
    if ( // r: LONG_SHL(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (!Binary.getResult(P(p)).similar(Binary.getVal1(P(p))) && (Binary.getVal2(P(p)).asIntConstant().value & 0x3f) <= 3 ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 360, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xAE00); // p.r = 174
        closure_r(p, c);
      }
    }
    if ( // szpr: LONG_SHL(LONG_SHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + (((VR(p) == VLR(p)) && (VR(p) < 32)) ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 407, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x11000000); // p.szpr = 34
        closure_szpr(p, c);
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
      if(BURS.DEBUG) trace(p, 629, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x7000000); // p.szpr = 14
        closure_szpr(p, c);
      }
    }
    // szpr: INT_SHR(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 123, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x7800000); // p.szpr = 15
      closure_szpr(p, c);
    }
    if ( // szpr: INT_SHR(riv,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + 13;
      if(BURS.DEBUG) trace(p, 345, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x8000000); // p.szpr = 16
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
    if ( // szpr: LONG_SHR(rlv,INT_AND(r,LONG_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 63 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 633, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x11800000); // p.szpr = 35
        closure_szpr(p, c);
      }
    }
    // szpr: LONG_SHR(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 200, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x12000000); // p.szpr = 36
      closure_szpr(p, c);
    }
    if ( // szpr: LONG_SHR(rlv,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + 13;
      if(BURS.DEBUG) trace(p, 361, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x12800000); // p.szpr = 37
        closure_szpr(p, c);
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
      if(BURS.DEBUG) trace(p, 394, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xA00); // p.r = 10
        closure_r(p, c);
      }
    }
    if ( // r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(13 /* load16_32 */) + (VR(p) == 16 && VLR(p) == 16 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 395, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xC00); // p.r = 12
        closure_r(p, c);
      }
    }
    if ( // szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
      rchild.getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 31 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 631, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x8800000); // p.szpr = 17
        closure_szpr(p, c);
      }
    }
    // szpr: INT_USHR(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 129, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x9000000); // p.szpr = 18
      closure_szpr(p, c);
    }
    if ( // szpr: INT_USHR(riv,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + 13;
      if(BURS.DEBUG) trace(p, 346, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x9800000); // p.szpr = 19
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
    if ( // szpr: LONG_USHR(rlv,LONG_AND(r,LONG_CONSTANT))
      rchild.getOpcode() == LONG_AND_opcode && 
      rchild.getChild2().getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (VRR(p) == 63 ? 23 : INFINITE);
      if(BURS.DEBUG) trace(p, 635, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x13000000); // p.szpr = 38
        closure_szpr(p, c);
      }
    }
    // szpr: LONG_USHR(rlv,riv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(7 /* riv */) + 23;
    if(BURS.DEBUG) trace(p, 206, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x13800000); // p.szpr = 39
      closure_szpr(p, c);
    }
    if ( // szpr: LONG_USHR(rlv,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + 13;
      if(BURS.DEBUG) trace(p, 362, c + 0, p.getCost(5) /* szpr */);
      if (c < p.getCost(5) /* szpr */) {
        p.setCost(5 /* szpr */, (char)(c));
        p.writePacked(0, 0xE07FFFFF, 0x14000000); // p.szpr = 40
        closure_szpr(p, c);
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
      if(BURS.DEBUG) trace(p, 263, c + 0, p.getCost(11) /* uload8 */);
      if (c < p.getCost(11) /* uload8 */) {
        p.setCost(11 /* uload8 */, (char)(c));
        p.writePacked(1, 0xFFFE3FFF, 0x4000); // p.uload8 = 1
        closure_uload8(p, c);
      }
    }
    if ( // r: INT_AND(load8_16_32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(12 /* load8_16_32 */) + (VR(p) == 0xff ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 264, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x800); // p.r = 8
        closure_r(p, c);
      }
    }
    if ( // r: INT_AND(load16_32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(13 /* load16_32 */) + (VR(p) == 0xffff ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 266, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xB00); // p.r = 11
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
      if(BURS.DEBUG) trace(p, 533, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x10); // p.bittest = 1
      }
    }
    if ( // bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(10 /* load32 */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + (VR(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 534, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x20); // p.bittest = 2
      }
    }
    if ( // bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLR(p) <= 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 396, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x30); // p.bittest = 3
      }
    }
    if ( // bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLRR(p) == 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 535, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x40); // p.bittest = 4
      }
    }
    if ( // bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(10 /* load32 */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + (VR(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 536, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x50); // p.bittest = 5
      }
    }
    if ( // bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((VR(p) == 1) && (VLR(p) <= 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 397, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x60); // p.bittest = 6
      }
    }
    if ( // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild).getCost(2 /* r */) + ((VLL(p) == 1) && (VLRR(p) == 31)? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 537, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x70); // p.bittest = 7
      }
    }
    if ( // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + (VLL(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 538, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x80); // p.bittest = 8
      }
    }
    if ( // bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + ((VRL(p) == 1) && (VRRR(p) == 31) ? 13:INFINITE);
      if(BURS.DEBUG) trace(p, 539, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0x90); // p.bittest = 9
      }
    }
    if ( // bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      rchild.getOpcode() == INT_SHL_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == INT_AND_opcode && 
      rchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + (VRL(p) == 1 ? 31:INFINITE);
      if(BURS.DEBUG) trace(p, 540, c + 0, p.getCost(18) /* bittest */);
      if (c < p.getCost(18) /* bittest */) {
        p.setCost(18 /* bittest */, (char)(c));
        p.writePacked(2, 0xFFFFFF0F, 0xA0); // p.bittest = 10
      }
    }
    // szpr: INT_AND(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 88, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x1000000); // p.szpr = 2
      closure_szpr(p, c);
    }
    // szp: INT_AND(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 89, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x2); // p.szp = 2
    }
    // szpr: INT_AND(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 90, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x1800000); // p.szpr = 3
      closure_szpr(p, c);
    }
    // szpr: INT_AND(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 91, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x2000000); // p.szpr = 4
      closure_szpr(p, c);
    }
    // szp: INT_AND(load8_16_32,riv)
    c = STATE(lchild).getCost(12 /* load8_16_32 */) + STATE(rchild).getCost(7 /* riv */) + 11;
    if(BURS.DEBUG) trace(p, 92, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x3); // p.szp = 3
    }
    // szp: INT_AND(r,load8_16_32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(12 /* load8_16_32 */) + 11;
    if(BURS.DEBUG) trace(p, 93, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x4); // p.szp = 4
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
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + ((Binary.getVal2(P(p)).asLongConstant().upper32() == 0) && (Binary.getVal2(P(p)).asLongConstant().lower32() == -1)? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 398, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x5300); // p.r = 83
        closure_r(p, c);
      }
    }
    if ( // r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
      lchild.getOpcode() == INT_2LONG_opcode && 
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(10 /* load32 */) + ((Binary.getVal2(P(p)).asLongConstant().upper32() == 0) && (Binary.getVal2(P(p)).asLongConstant().lower32() == -1)? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 399, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x5400); // p.r = 84
        closure_r(p, c);
      }
    }
    // szpr: LONG_AND(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 168, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xB800000); // p.szpr = 23
      closure_szpr(p, c);
    }
    // szpr: LONG_AND(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 9;
    if(BURS.DEBUG) trace(p, 169, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xC000000); // p.szpr = 24
      closure_szpr(p, c);
    }
    // szp: LONG_AND(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 11;
    if(BURS.DEBUG) trace(p, 170, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x6); // p.szp = 6
    }
    // szpr: LONG_AND(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 171, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xC800000); // p.szpr = 25
      closure_szpr(p, c);
    }
    // szpr: LONG_AND(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 172, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xD000000); // p.szpr = 26
      closure_szpr(p, c);
    }
    // szp: LONG_AND(load8_16_32_64,rlv)
    c = STATE(lchild).getCost(25 /* load8_16_32_64 */) + STATE(rchild).getCost(8 /* rlv */) + 11;
    if(BURS.DEBUG) trace(p, 173, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x7); // p.szp = 7
    }
    // szp: LONG_AND(r,load8_16_32_64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(25 /* load8_16_32_64 */) + 11;
    if(BURS.DEBUG) trace(p, 174, c + 0, p.getCost(6) /* szp */);
    if (c < p.getCost(6) /* szp */) {
      p.setCost(6 /* szp */, (char)(c));
      p.writePacked(1, 0xFFFFFFF0, 0x8); // p.szp = 8
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
    if(BURS.DEBUG) trace(p, 115, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x3800000); // p.szpr = 7
      closure_szpr(p, c);
    }
    // szpr: INT_OR(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 116, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x4000000); // p.szpr = 8
      closure_szpr(p, c);
    }
    // szpr: INT_OR(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 117, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x4800000); // p.szpr = 9
      closure_szpr(p, c);
    }
    if ( // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == INT_USHR_opcode && 
      rchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + (Binary.getVal1(PL(p)).similar(Binary.getVal1(PR(p))) && ((-VLR(p)) & 0x1f) == (VRR(p)&0x1f) ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 620, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x6E00); // p.r = 110
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
      if(BURS.DEBUG) trace(p, 621, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x6F00); // p.r = 111
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
      if(BURS.DEBUG) trace(p, 622, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7000); // p.r = 112
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
      if(BURS.DEBUG) trace(p, 623, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7100); // p.r = 113
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
      if(BURS.DEBUG) trace(p, 624, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7200); // p.r = 114
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
      if(BURS.DEBUG) trace(p, 626, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7300); // p.r = 115
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
      if(BURS.DEBUG) trace(p, 627, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7400); // p.r = 116
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
      if(BURS.DEBUG) trace(p, 625, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7500); // p.r = 117
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
    // szpr: LONG_OR(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 191, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xE000000); // p.szpr = 28
      closure_szpr(p, c);
    }
    // szpr: LONG_OR(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 192, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xE800000); // p.szpr = 29
      closure_szpr(p, c);
    }
    // szpr: LONG_OR(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 193, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xF000000); // p.szpr = 30
      closure_szpr(p, c);
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
    if(BURS.DEBUG) trace(p, 130, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xA000000); // p.szpr = 20
      closure_szpr(p, c);
    }
    // szpr: INT_XOR(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 131, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xA800000); // p.szpr = 21
      closure_szpr(p, c);
    }
    // szpr: INT_XOR(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 132, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0xB000000); // p.szpr = 22
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
    if(BURS.DEBUG) trace(p, 342, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6900); // p.r = 105
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
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 358, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xA800); // p.r = 168
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
    // szpr: LONG_XOR(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 207, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x14800000); // p.szpr = 41
      closure_szpr(p, c);
    }
    // szpr: LONG_XOR(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 208, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x15000000); // p.szpr = 42
      closure_szpr(p, c);
    }
    // szpr: LONG_XOR(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 209, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x15800000); // p.szpr = 43
      closure_szpr(p, c);
    }
  }

  /**
   * Labels INT_2ADDRZerExt tree node
   * @param p node to label
   */
  private static void label_INT_2ADDRZerExt(AbstractBURS_TreeNode p) {
    p.initCost();
    AbstractBURS_TreeNode lchild;
    lchild = p.getChild1();
    label(lchild);
    int c;
    // r: INT_2ADDRZerExt(r)
    c = STATE(lchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 313, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5500); // p.r = 85
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
    c = STATE(lchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 311, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5100); // p.r = 81
      closure_r(p, c);
    }
    // r: INT_2LONG(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 13;
    if(BURS.DEBUG) trace(p, 312, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5200); // p.r = 82
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
    if(BURS.DEBUG) trace(p, 371, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xDC00); // p.r = 220
      closure_r(p, c);
    }
    // r: INT_2FLOAT(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 372, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xDD00); // p.r = 221
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
    if(BURS.DEBUG) trace(p, 373, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xDE00); // p.r = 222
      closure_r(p, c);
    }
    // r: INT_2DOUBLE(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 374, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xDF00); // p.r = 223
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
    if(BURS.DEBUG) trace(p, 349, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8F00); // p.r = 143
      closure_r(p, c);
    }
    // r: LONG_2INT(load64)
    c = STATE(lchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 350, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9000); // p.r = 144
      closure_r(p, c);
    }
    // load32: LONG_2INT(load64)
    c = STATE(lchild).getCost(20 /* load64 */) + 0;
    if(BURS.DEBUG) trace(p, 351, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFC7FF, 0x2000); // p.load32 = 4
      closure_load32(p, c);
    }
    if ( // r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + (VLR(p) == 32 ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 401, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x9100); // p.r = 145
        closure_r(p, c);
      }
    }
    if ( // r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + (VLR(p) == 32 ? 13 : INFINITE);
      if(BURS.DEBUG) trace(p, 402, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x9200); // p.r = 146
        closure_r(p, c);
      }
    }
    if ( // r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(20 /* load64 */) + (VLR(p) == 32 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 403, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x9300); // p.r = 147
        closure_r(p, c);
      }
    }
    if ( // r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(20 /* load64 */) + (VLR(p) == 32 ? 15 : INFINITE);
      if(BURS.DEBUG) trace(p, 404, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x9400); // p.r = 148
        closure_r(p, c);
      }
    }
    if ( // load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(20 /* load64 */) + (VLR(p) == 32 ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 405, c + 0, p.getCost(10) /* load32 */);
      if (c < p.getCost(10) /* load32 */) {
        p.setCost(10 /* load32 */, (char)(c));
        p.writePacked(1, 0xFFFFC7FF, 0x2800); // p.load32 = 5
        closure_load32(p, c);
      }
    }
    if ( // load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(20 /* load64 */) + (VLR(p) == 32 ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 406, c + 0, p.getCost(10) /* load32 */);
      if (c < p.getCost(10) /* load32 */) {
        p.setCost(10 /* load32 */, (char)(c));
        p.writePacked(1, 0xFFFFC7FF, 0x3000); // p.load32 = 6
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
    if(BURS.DEBUG) trace(p, 367, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xCB00); // p.r = 203
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
    if(BURS.DEBUG) trace(p, 368, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xCC00); // p.r = 204
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
    if(BURS.DEBUG) trace(p, 379, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE400); // p.r = 228
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
    if(BURS.DEBUG) trace(p, 380, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE500); // p.r = 229
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
    if(BURS.DEBUG) trace(p, 375, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE000); // p.r = 224
      closure_r(p, c);
    }
    // r: FLOAT_2DOUBLE(float_load)
    c = STATE(lchild).getCost(26 /* float_load */) + 15;
    if(BURS.DEBUG) trace(p, 376, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE100); // p.r = 225
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
    if(BURS.DEBUG) trace(p, 381, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE600); // p.r = 230
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
    if(BURS.DEBUG) trace(p, 382, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE700); // p.r = 231
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
    if(BURS.DEBUG) trace(p, 377, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE200); // p.r = 226
      closure_r(p, c);
    }
    // r: DOUBLE_2FLOAT(double_load)
    c = STATE(lchild).getCost(27 /* double_load */) + 15;
    if(BURS.DEBUG) trace(p, 378, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE300); // p.r = 227
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
    if(BURS.DEBUG) trace(p, 265, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x900); // p.r = 9
      closure_r(p, c);
    }
    // r: INT_2BYTE(r)
    c = STATE(lchild).getCost(2 /* r */) + 15;
    if(BURS.DEBUG) trace(p, 309, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x4F00); // p.r = 79
      closure_r(p, c);
    }
    // r: INT_2BYTE(load8_16_32)
    c = STATE(lchild).getCost(12 /* load8_16_32 */) + 17;
    if(BURS.DEBUG) trace(p, 310, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5000); // p.r = 80
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
    if(BURS.DEBUG) trace(p, 317, c + 0, p.getCost(5) /* szpr */);
    if (c < p.getCost(5) /* szpr */) {
      p.setCost(5 /* szpr */, (char)(c));
      p.writePacked(0, 0xE07FFFFF, 0x800000); // p.szpr = 1
      closure_szpr(p, c);
    }
    // uload16: INT_2USHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 0;
    if(BURS.DEBUG) trace(p, 318, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x100000); // p.uload16 = 1
      closure_uload16(p, c);
    }
    // r: INT_2USHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 15;
    if(BURS.DEBUG) trace(p, 319, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5800); // p.r = 88
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
    if(BURS.DEBUG) trace(p, 314, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5600); // p.r = 86
      closure_r(p, c);
    }
    // r: INT_2SHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 17;
    if(BURS.DEBUG) trace(p, 315, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5700); // p.r = 87
      closure_r(p, c);
    }
    // sload16: INT_2SHORT(load16_32)
    c = STATE(lchild).getCost(13 /* load16_32 */) + 0;
    if(BURS.DEBUG) trace(p, 316, c + 0, p.getCost(22) /* sload16 */);
    if (c < p.getCost(22) /* sload16 */) {
      p.setCost(22 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x20000); // p.sload16 = 1
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
    if(BURS.DEBUG) trace(p, 58, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD00); // p.r = 13
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
      if(BURS.DEBUG) trace(p, 49, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x2E); // p.stm = 46
      }
    }
    if ( // stm: RETURN(INT_CONSTANT)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = 11;
      if(BURS.DEBUG) trace(p, 50, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x2F); // p.stm = 47
      }
    }
    // stm: RETURN(r)
    c = STATE(lchild).getCost(2 /* r */) + 13;
    if(BURS.DEBUG) trace(p, 268, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x30); // p.stm = 48
    }
    if ( // stm: RETURN(LONG_CONSTANT)
      lchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = 11;
      if(BURS.DEBUG) trace(p, 51, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 259, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 43, 11 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 304, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x3D00); // p.r = 61
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
    if(BURS.DEBUG) trace(p, 72, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x2700); // p.r = 39
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_INT(r,riv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(7 /* riv */) + 13;
    if(BURS.DEBUG) trace(p, 73, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFF0FF, 0x100); // p.boolcmp = 1
    }
    if ( // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && CMP_TO_TEST(BooleanCmp.getCond(P(p))) ? 37:INFINITE);
      if(BURS.DEBUG) trace(p, 281, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2800); // p.r = 40
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && CMP_TO_TEST(BooleanCmp.getCond(P(p))) ? 11:INFINITE);
      if(BURS.DEBUG) trace(p, 282, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0x200); // p.boolcmp = 2
      }
    }
    if ( // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isLESS() ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 283, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2900); // p.r = 41
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isLESS() ? 16 : INFINITE);
      if(BURS.DEBUG) trace(p, 284, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2A00); // p.r = 42
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isGREATER_EQUAL() ? 22 : INFINITE);
      if(BURS.DEBUG) trace(p, 285, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2B00); // p.r = 43
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + (VR(p) == 0 && BooleanCmp.getCond(P(p)).isGREATER_EQUAL() ? 27 : INFINITE);
      if(BURS.DEBUG) trace(p, 286, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2C00); // p.r = 44
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + isZERO(VR(p), 26);
      if(BURS.DEBUG) trace(p, 287, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2D00); // p.r = 45
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + isZERO(VR(p), 0);
      if(BURS.DEBUG) trace(p, 288, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0x300); // p.boolcmp = 3
      }
    }
    if ( // r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + (VR(p) == 0 && EQ_NE(BooleanCmp.getCond(P(p)))?26:INFINITE);
      if(BURS.DEBUG) trace(p, 289, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2E00); // p.r = 46
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + (VR(p) == 0 && EQ_NE(BooleanCmp.getCond(P(p)))?0:INFINITE);
      if(BURS.DEBUG) trace(p, 290, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0x400); // p.boolcmp = 4
      }
    }
    if ( // r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + ((VR(p) == 0 || VR(p) == 1) && EQ_NE(BooleanCmp.getCond(P(p))) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 291, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2F00); // p.r = 47
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + ((VR(p) == 0 || VR(p) == 1) && EQ_NE(BooleanCmp.getCond(P(p))) ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 292, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0x500); // p.boolcmp = 5
      }
    }
    if ( // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 1 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 293, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3000); // p.r = 48
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 0 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 1 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 294, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0x600); // p.boolcmp = 6
      }
    }
    if ( // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 1 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 0 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 295, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3100); // p.r = 49
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      rchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + ((VR(p) == 1 && BooleanCmp.getCond(P(p)).isNOT_EQUAL()) || (VR(p) == 0 && BooleanCmp.getCond(P(p)).isEQUAL()) ? 0 : INFINITE);
      if(BURS.DEBUG) trace(p, 296, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0x700); // p.boolcmp = 7
      }
    }
    // r: BOOLEAN_CMP_INT(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 41;
    if(BURS.DEBUG) trace(p, 74, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x3200); // p.r = 50
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_INT(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 75, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFF0FF, 0x800); // p.boolcmp = 8
    }
    // r: BOOLEAN_CMP_INT(r,load32)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(10 /* load32 */) + 41;
    if(BURS.DEBUG) trace(p, 76, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x3300); // p.r = 51
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_INT(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 77, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFF0FF, 0x900); // p.boolcmp = 9
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
    // r: BOOLEAN_CMP_LONG(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 39;
    if(BURS.DEBUG) trace(p, 78, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x3400); // p.r = 52
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_LONG(r,rlv)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(8 /* rlv */) + 13;
    if(BURS.DEBUG) trace(p, 79, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFF0FF, 0xA00); // p.boolcmp = 10
    }
    if ( // r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) && CMP_TO_TEST(BooleanCmp.getCond(P(p))) ? 37:INFINITE);
      if(BURS.DEBUG) trace(p, 297, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3500); // p.r = 53
        closure_r(p, c);
      }
    }
    if ( // boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) && CMP_TO_TEST(BooleanCmp.getCond(P(p))) ? 11:INFINITE);
      if(BURS.DEBUG) trace(p, 298, c + 0, p.getCost(19) /* boolcmp */);
      if (c < p.getCost(19) /* boolcmp */) {
        p.setCost(19 /* boolcmp */, (char)(c));
        p.writePacked(2, 0xFFFFF0FF, 0xB00); // p.boolcmp = 11
      }
    }
    if ( // r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) && BooleanCmp.getCond(P(p)).isLESS() ? 11 : INFINITE);
      if(BURS.DEBUG) trace(p, 299, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3600); // p.r = 54
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) && BooleanCmp.getCond(P(p)).isLESS() ? 16 : INFINITE);
      if(BURS.DEBUG) trace(p, 300, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3700); // p.r = 55
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) && BooleanCmp.getCond(P(p)).isGREATER_EQUAL() ? 22 : INFINITE);
      if(BURS.DEBUG) trace(p, 301, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3800); // p.r = 56
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) && BooleanCmp.getCond(P(p)).isGREATER_EQUAL() ? 27 : INFINITE);
      if(BURS.DEBUG) trace(p, 302, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3900); // p.r = 57
        closure_r(p, c);
      }
    }
    if ( // r: BOOLEAN_CMP_LONG(cz,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + ((LV(BooleanCmp.getVal2(P(p))) == 0) ? 26 : INFINITE);
      if(BURS.DEBUG) trace(p, 303, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3A00); // p.r = 58
        closure_r(p, c);
      }
    }
    // r: BOOLEAN_CMP_LONG(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 41;
    if(BURS.DEBUG) trace(p, 80, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x3B00); // p.r = 59
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_LONG(load64,rlv)
    c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 81, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFF0FF, 0xC00); // p.boolcmp = 12
    }
    // r: BOOLEAN_CMP_LONG(r,load64)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(20 /* load64 */) + 41;
    if(BURS.DEBUG) trace(p, 82, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x3C00); // p.r = 60
      closure_r(p, c);
    }
    // boolcmp: BOOLEAN_CMP_LONG(rlv,load64)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(20 /* load64 */) + 15;
    if(BURS.DEBUG) trace(p, 83, c + 0, p.getCost(19) /* boolcmp */);
    if (c < p.getCost(19) /* boolcmp */) {
      p.setCost(19 /* boolcmp */, (char)(c));
      p.writePacked(2, 0xFFFFF0FF, 0xD00); // p.boolcmp = 13
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
    // r: BYTE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 20;
    if(BURS.DEBUG) trace(p, 137, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8300); // p.r = 131
      closure_r(p, c);
    }
    // sload8: BYTE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 138, c + 0, p.getCost(24) /* sload8 */);
    if (c < p.getCost(24) /* sload8 */) {
      p.setCost(24 /* sload8 */, (char)(c));
      p.writePacked(2, 0xFE7FFFFF, 0x1000000); // p.sload8 = 2
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
    // r: UBYTE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 142, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8600); // p.r = 134
      closure_r(p, c);
    }
    // uload8: UBYTE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 143, c + 0, p.getCost(11) /* uload8 */);
    if (c < p.getCost(11) /* uload8 */) {
      p.setCost(11 /* uload8 */, (char)(c));
      p.writePacked(1, 0xFFFE3FFF, 0xC000); // p.uload8 = 3
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
    // r: SHORT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 20;
    if(BURS.DEBUG) trace(p, 147, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8900); // p.r = 137
      closure_r(p, c);
    }
    // sload16: SHORT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 148, c + 0, p.getCost(22) /* sload16 */);
    if (c < p.getCost(22) /* sload16 */) {
      p.setCost(22 /* sload16 */, (char)(c));
      p.writePacked(2, 0xFFF1FFFF, 0x60000); // p.sload16 = 3
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
    // r: USHORT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 152, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x8C00); // p.r = 140
      closure_r(p, c);
    }
    // uload16: USHORT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 153, c + 0, p.getCost(23) /* uload16 */);
    if (c < p.getCost(23) /* uload16 */) {
      p.setCost(23 /* uload16 */, (char)(c));
      p.writePacked(2, 0xFF8FFFFF, 0x300000); // p.uload16 = 3
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
    // r: INT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 106, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5E00); // p.r = 94
      closure_r(p, c);
    }
    // r: INT_LOAD(rlv,address1scaledreg)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 15;
    if(BURS.DEBUG) trace(p, 107, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x5F00); // p.r = 95
      closure_r(p, c);
    }
    // r: INT_LOAD(address1scaledreg,rlv)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 108, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6000); // p.r = 96
      closure_r(p, c);
    }
    // r: INT_LOAD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(16 /* address1reg */) + 15;
    if(BURS.DEBUG) trace(p, 109, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6100); // p.r = 97
      closure_r(p, c);
    }
    // r: INT_LOAD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 15;
    if(BURS.DEBUG) trace(p, 110, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x6200); // p.r = 98
      closure_r(p, c);
    }
    if ( // r: INT_LOAD(address,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address */) + 15;
      if(BURS.DEBUG) trace(p, 328, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x6300); // p.r = 99
        closure_r(p, c);
      }
    }
    // load32: INT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 157, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFC7FF, 0x1000); // p.load32 = 2
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
    // load64: LONG_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 159, c + 0, p.getCost(20) /* load64 */);
    if (c < p.getCost(20) /* load64 */) {
      p.setCost(20 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x1000); // p.load64 = 1
      closure_load64(p, c);
    }
    // r: LONG_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 181, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9B00); // p.r = 155
      closure_r(p, c);
    }
    // r: LONG_LOAD(rlv,address1scaledreg)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 15;
    if(BURS.DEBUG) trace(p, 182, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9C00); // p.r = 156
      closure_r(p, c);
    }
    // r: LONG_LOAD(address1scaledreg,rlv)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 183, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9D00); // p.r = 157
      closure_r(p, c);
    }
    // r: LONG_LOAD(address1scaledreg,address1reg)
    c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild).getCost(16 /* address1reg */) + 15;
    if(BURS.DEBUG) trace(p, 184, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9E00); // p.r = 158
      closure_r(p, c);
    }
    // r: LONG_LOAD(address1reg,address1scaledreg)
    c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild).getCost(15 /* address1scaledreg */) + 15;
    if(BURS.DEBUG) trace(p, 185, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x9F00); // p.r = 159
      closure_r(p, c);
    }
    if ( // r: LONG_LOAD(address,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address */) + 15;
      if(BURS.DEBUG) trace(p, 353, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xA000); // p.r = 160
        closure_r(p, c);
      }
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
    if(BURS.DEBUG) trace(p, 243, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD600); // p.r = 214
      closure_r(p, c);
    }
    // r: FLOAT_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 244, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD700); // p.r = 215
      closure_r(p, c);
    }
    // float_load: FLOAT_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 245, c + 0, p.getCost(26) /* float_load */);
    if (c < p.getCost(26) /* float_load */) {
      p.setCost(26 /* float_load */, (char)(c));
      p.writePacked(2, 0xC7FFFFFF, 0x8000000); // p.float_load = 1
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
    if(BURS.DEBUG) trace(p, 232, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xCF00); // p.r = 207
      closure_r(p, c);
    }
    // r: DOUBLE_LOAD(riv,rlv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 233, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD000); // p.r = 208
      closure_r(p, c);
    }
    // r: DOUBLE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 15;
    if(BURS.DEBUG) trace(p, 234, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xD100); // p.r = 209
      closure_r(p, c);
    }
    // double_load: DOUBLE_LOAD(riv,riv)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(7 /* riv */) + 0;
    if(BURS.DEBUG) trace(p, 235, c + 0, p.getCost(27) /* double_load */);
    if (c < p.getCost(27) /* double_load */) {
      p.setCost(27 /* double_load */, (char)(c));
      p.writePacked(3, 0xFFFFFFF8, 0x1); // p.double_load = 1
    }
    // double_load: DOUBLE_LOAD(rlv,rlv)
    c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild).getCost(8 /* rlv */) + 0;
    if(BURS.DEBUG) trace(p, 238, c + 0, p.getCost(27) /* double_load */);
    if (c < p.getCost(27) /* double_load */) {
      p.setCost(27 /* double_load */, (char)(c));
      p.writePacked(3, 0xFFFFFFF8, 0x2); // p.double_load = 2
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
      if(BURS.DEBUG) trace(p, 423, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x4F); // p.stm = 79
      }
    }
    if ( // stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == BOOLEAN_NOT_opcode && 
      lchild.getChild1().getOpcode() == UBYTE_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 541, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x51); // p.stm = 81
      }
    }
    if ( // stm: BYTE_STORE(riv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 425, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x53); // p.stm = 83
      }
    }
    if ( // stm: BYTE_STORE(load8,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(21 /* load8 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 25;
      if(BURS.DEBUG) trace(p, 426, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x54); // p.stm = 84
      }
    }
    if ( // stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2BYTE_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 572, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x57); // p.stm = 87
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
      if(BURS.DEBUG) trace(p, 408, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x16); // p.stm = 22
      }
    }
    if ( // stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(14 /* load16 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 25;
      if(BURS.DEBUG) trace(p, 409, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x17); // p.stm = 23
      }
    }
    if ( // stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 410, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x18); // p.stm = 24
      }
    }
    if ( // stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 411, c + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 574, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x59); // p.stm = 89
      }
    }
    if ( // stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_2USHORT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 576, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5B); // p.stm = 91
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
      if(BURS.DEBUG) trace(p, 580, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5D); // p.stm = 93
      }
    }
    if ( // stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_ADD_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 600, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x5E); // p.stm = 94
      }
    }
    if ( // stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 582, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x61); // p.stm = 97
      }
    }
    if ( // stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 602, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x62); // p.stm = 98
      }
    }
    if ( // stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NEG_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 543, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x75); // p.stm = 117
      }
    }
    if ( // stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_NOT_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 545, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x77); // p.stm = 119
      }
    }
    if ( // stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 584, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x79); // p.stm = 121
      }
    }
    if ( // stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_OR_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 604, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7A); // p.stm = 122
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
      if(BURS.DEBUG) trace(p, 636, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7D); // p.stm = 125
      }
    }
    if ( // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHL_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 547, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x7E); // p.stm = 126
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
      if(BURS.DEBUG) trace(p, 638, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x81); // p.stm = 129
      }
    }
    if ( // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SHR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 549, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x82); // p.stm = 130
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 434, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x85); // p.stm = 133
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(rlv,address1scaledreg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(15 /* address1scaledreg */) + 15;
      if(BURS.DEBUG) trace(p, 435, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x86); // p.stm = 134
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 436, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x87); // p.stm = 135
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2()).getCost(16 /* address1reg */) + 15;
      if(BURS.DEBUG) trace(p, 437, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x88); // p.stm = 136
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(16 /* address1reg */) + STATE(rchild.getChild2()).getCost(15 /* address1scaledreg */) + 15;
      if(BURS.DEBUG) trace(p, 438, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x89); // p.stm = 137
      }
    }
    if ( // stm: INT_STORE(riv,OTHER_OPERAND(address,LONG_CONSTANT))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(17 /* address */) + 15;
      if(BURS.DEBUG) trace(p, 630, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8A); // p.stm = 138
      }
    }
    if ( // stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 586, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8B); // p.stm = 139
      }
    }
    if ( // stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_SUB_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 27);
      if(BURS.DEBUG) trace(p, 606, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8C); // p.stm = 140
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
      if(BURS.DEBUG) trace(p, 640, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x8F); // p.stm = 143
      }
    }
    if ( // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_USHR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 551, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x90); // p.stm = 144
      }
    }
    if ( // stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild1().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 588, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x93); // p.stm = 147
      }
    }
    if ( // stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == INT_XOR_opcode && 
      lchild.getChild2().getOpcode() == INT_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 608, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x94); // p.stm = 148
      }
    }
    if ( // stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_2INT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 15;
      if(BURS.DEBUG) trace(p, 578, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x97); // p.stm = 151
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
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 590, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x99); // p.stm = 153
      }
    }
    if ( // stm: LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_ADD_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 610, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9A); // p.stm = 154
      }
    }
    if ( // stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 592, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9D); // p.stm = 157
      }
    }
    if ( // stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 612, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x9E); // p.stm = 158
      }
    }
    if ( // stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NEG_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 553, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA3); // p.stm = 163
      }
    }
    if ( // stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_NOT_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 555, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA5); // p.stm = 165
      }
    }
    if ( // stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 594, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA7); // p.stm = 167
      }
    }
    if ( // stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_OR_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 614, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xA8); // p.stm = 168
      }
    }
    if ( // stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHL_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 63 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 642, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAB); // p.stm = 171
      }
    }
    if ( // stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHL_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 557, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAC); // p.stm = 172
      }
    }
    if ( // stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      lchild.getChild2().getOpcode() == INT_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 63 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 644, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xAF); // p.stm = 175
      }
    }
    if ( // stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_SHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      lchild.getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 559, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB0); // p.stm = 176
      }
    }
    if ( // stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 442, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB3); // p.stm = 179
      }
    }
    if ( // stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,address1scaledreg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(15 /* address1scaledreg */) + 15;
      if(BURS.DEBUG) trace(p, 443, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB4); // p.stm = 180
      }
    }
    if ( // stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 15;
      if(BURS.DEBUG) trace(p, 444, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB5); // p.stm = 181
      }
    }
    if ( // stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,address1reg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2()).getCost(16 /* address1reg */) + 15;
      if(BURS.DEBUG) trace(p, 445, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB6); // p.stm = 182
      }
    }
    if ( // stm: LONG_STORE(rlv,OTHER_OPERAND(address1reg,address1scaledreg))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(16 /* address1reg */) + STATE(rchild.getChild2()).getCost(15 /* address1scaledreg */) + 15;
      if(BURS.DEBUG) trace(p, 446, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB7); // p.stm = 183
      }
    }
    if ( // stm: LONG_STORE(rlv,OTHER_OPERAND(address,LONG_CONSTANT))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(17 /* address */) + 15;
      if(BURS.DEBUG) trace(p, 634, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB8); // p.stm = 184
      }
    }
    if ( // stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_SUB_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 596, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xB9); // p.stm = 185
      }
    }
    if ( // stm: LONG_STORE(LONG_SUB(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_SUB_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 27);
      if(BURS.DEBUG) trace(p, 616, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBA); // p.stm = 186
      }
    }
    if ( // stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      lchild.getChild2().getOpcode() == LONG_AND_opcode && 
      lchild.getChild2().getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(lchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + (ADDRESS_EQUAL(P(p), PLL(p), VLRR(p) == 63 ? 27 : INFINITE));
      if(BURS.DEBUG) trace(p, 646, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBD); // p.stm = 189
      }
    }
    if ( // stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      lchild.getOpcode() == LONG_USHR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      lchild.getChild2().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild1().getChild2()).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 561, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xBE); // p.stm = 190
      }
    }
    if ( // stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild1().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild1().getChild2()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLL(p), 17);
      if(BURS.DEBUG) trace(p, 598, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC1); // p.stm = 193
      }
    }
    if ( // stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      lchild.getOpcode() == LONG_XOR_opcode && 
      lchild.getChild2().getOpcode() == LONG_LOAD_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(2 /* r */) + STATE(lchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2().getChild2()).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + ADDRESS_EQUAL(P(p), PLR(p), 17);
      if(BURS.DEBUG) trace(p, 618, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC2); // p.stm = 194
      }
    }
    if ( // stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 475, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xE0); // p.stm = 224
      }
    }
    if ( // stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 32;
      if(BURS.DEBUG) trace(p, 476, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xE1); // p.stm = 225
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
      if(BURS.DEBUG) trace(p, 456, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xCE); // p.stm = 206
      }
    }
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 457, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xCF); // p.stm = 207
      }
    }
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 458, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD0); // p.stm = 208
      }
    }
    if ( // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 459, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xD1); // p.stm = 209
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
      if(BURS.DEBUG) trace(p, 447, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC5); // p.stm = 197
      }
    }
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 448, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC6); // p.stm = 198
      }
    }
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(7 /* riv */) + 17;
      if(BURS.DEBUG) trace(p, 449, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC7); // p.stm = 199
      }
    }
    if ( // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(8 /* rlv */) + 17;
      if(BURS.DEBUG) trace(p, 450, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0xC8); // p.stm = 200
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
      if(BURS.DEBUG) trace(p, 485, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1700); // p.r = 23
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 486, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1800); // p.r = 24
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 487, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1900); // p.r = 25
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 488, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1A00); // p.r = 26
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 489, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1B00); // p.r = 27
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild1()).getCost(16 /* address1reg */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 490, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1C00); // p.r = 28
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 491, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1D00); // p.r = 29
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 501, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1E00); // p.r = 30
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
      lchild.getOpcode() == INT_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(17 /* address */) + STATE(rchild.getChild2().getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2().getChild2()).getCost(7 /* riv */) + 67;
      if(BURS.DEBUG) trace(p, 503, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1F00); // p.r = 31
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
    if ( // r: ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 492, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2000); // p.r = 32
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 493, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2100); // p.r = 33
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 494, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2200); // p.r = 34
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild1()).getCost(16 /* address1reg */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 495, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2300); // p.r = 35
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(16 /* address1reg */) + STATE(rchild.getChild1()).getCost(15 /* address1scaledreg */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 496, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2400); // p.r = 36
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(17 /* address */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 502, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2500); // p.r = 37
        closure_r(p, c);
      }
    }
    if ( // r: ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv)))
      lchild.getOpcode() == LONG_CONSTANT_opcode && 
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(rchild.getChild1()).getCost(17 /* address */) + STATE(rchild.getChild2().getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2().getChild2()).getCost(8 /* rlv */) + 67;
      if(BURS.DEBUG) trace(p, 504, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x2600); // p.r = 38
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
    if(BURS.DEBUG) trace(p, 59, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE00); // p.r = 14
      closure_r(p, c);
    }
    if ( // r: CALL(BRANCH_TARGET,any)
      lchild.getOpcode() == BRANCH_TARGET_opcode  
    ) {
      c = STATE(rchild).getCost(9 /* any */) + 13;
      if(BURS.DEBUG) trace(p, 479, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF00); // p.r = 15
        closure_r(p, c);
      }
    }
    if ( // r: CALL(INT_LOAD(riv,riv),any)
      lchild.getOpcode() == INT_LOAD_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild).getCost(9 /* any */) + 11;
      if(BURS.DEBUG) trace(p, 482, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1000); // p.r = 16
        closure_r(p, c);
      }
    }
    if ( // r: CALL(INT_CONSTANT,any)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(rchild).getCost(9 /* any */) + 23;
      if(BURS.DEBUG) trace(p, 480, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1100); // p.r = 17
        closure_r(p, c);
      }
    }
    if ( // r: CALL(LONG_LOAD(rlv,rlv),any)
      lchild.getOpcode() == LONG_LOAD_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(8 /* rlv */) + STATE(lchild.getChild2()).getCost(8 /* rlv */) + STATE(rchild).getCost(9 /* any */) + 11;
      if(BURS.DEBUG) trace(p, 483, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1200); // p.r = 18
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
    if(BURS.DEBUG) trace(p, 60, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0x1300); // p.r = 19
      closure_r(p, c);
    }
    if ( // r: SYSCALL(INT_LOAD(riv,riv),any)
      lchild.getOpcode() == INT_LOAD_opcode  
    ) {
      c = STATE(lchild.getChild1()).getCost(7 /* riv */) + STATE(lchild.getChild2()).getCost(7 /* riv */) + STATE(rchild).getCost(9 /* any */) + 11;
      if(BURS.DEBUG) trace(p, 484, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1400); // p.r = 20
        closure_r(p, c);
      }
    }
    if ( // r: SYSCALL(INT_CONSTANT,any)
      lchild.getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(rchild).getCost(9 /* any */) + 23;
      if(BURS.DEBUG) trace(p, 481, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x1500); // p.r = 21
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
    if(BURS.DEBUG) trace(p, 30, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 31, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 32, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 61, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 38, 11 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 34, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 52, 15 + 0, p.getCost(2) /* r */);
    if (15 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(15));
      p.writePacked(0, 0xFFFE00FF, 0x1600); // p.r = 22
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
      if(BURS.DEBUG) trace(p, 261, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x11); // p.stm = 17
      }
    }
    if ( // stm: TRAP_IF(r,LONG_CONSTANT)
      rchild.getOpcode() == LONG_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + 10;
      if(BURS.DEBUG) trace(p, 262, c + 0, p.getCost(1) /* stm */);
      if (c < p.getCost(1) /* stm */) {
        p.setCost(1 /* stm */, (char)(c));
        p.writePacked(0, 0xFFFFFF00, 0x12); // p.stm = 18
      }
    }
    // stm: TRAP_IF(r,r)
    c = STATE(lchild).getCost(2 /* r */) + STATE(rchild).getCost(2 /* r */) + 10;
    if(BURS.DEBUG) trace(p, 55, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x13); // p.stm = 19
    }
    // stm: TRAP_IF(load32,riv)
    c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild).getCost(7 /* riv */) + 15;
    if(BURS.DEBUG) trace(p, 56, c + 0, p.getCost(1) /* stm */);
    if (c < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(c));
      p.writePacked(0, 0xFFFFFF00, 0x14); // p.stm = 20
    }
    // stm: TRAP_IF(riv,load32)
    c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild).getCost(10 /* load32 */) + 15;
    if(BURS.DEBUG) trace(p, 57, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 42, 10 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 48, 11 + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 383, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE800); // p.r = 232
      closure_r(p, c);
    }
    // load32: FLOAT_AS_INT_BITS(float_load)
    c = STATE(lchild).getCost(26 /* float_load */) + 0;
    if(BURS.DEBUG) trace(p, 384, c + 0, p.getCost(10) /* load32 */);
    if (c < p.getCost(10) /* load32 */) {
      p.setCost(10 /* load32 */, (char)(c));
      p.writePacked(1, 0xFFFFC7FF, 0x3800); // p.load32 = 7
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
    if(BURS.DEBUG) trace(p, 387, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xEA00); // p.r = 234
      closure_r(p, c);
    }
    // float_load: INT_BITS_AS_FLOAT(load32)
    c = STATE(lchild).getCost(10 /* load32 */) + 0;
    if(BURS.DEBUG) trace(p, 388, c + 0, p.getCost(26) /* float_load */);
    if (c < p.getCost(26) /* float_load */) {
      p.setCost(26 /* float_load */, (char)(c));
      p.writePacked(2, 0xC7FFFFFF, 0x20000000); // p.float_load = 4
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
    if(BURS.DEBUG) trace(p, 385, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xE900); // p.r = 233
      closure_r(p, c);
    }
    // load64: DOUBLE_AS_LONG_BITS(double_load)
    c = STATE(lchild).getCost(27 /* double_load */) + 0;
    if(BURS.DEBUG) trace(p, 386, c + 0, p.getCost(20) /* load64 */);
    if (c < p.getCost(20) /* load64 */) {
      p.setCost(20 /* load64 */, (char)(c));
      p.writePacked(2, 0xFFFF8FFF, 0x5000); // p.load64 = 5
      closure_load64(p, c);
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
    if(BURS.DEBUG) trace(p, 389, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xEB00); // p.r = 235
      closure_r(p, c);
    }
    // double_load: LONG_BITS_AS_DOUBLE(load64)
    c = STATE(lchild).getCost(20 /* load64 */) + 0;
    if(BURS.DEBUG) trace(p, 390, c + 0, p.getCost(27) /* double_load */);
    if (c < p.getCost(27) /* double_load */) {
      p.setCost(27 /* double_load */, (char)(c));
      p.writePacked(3, 0xFFFFFFF8, 0x5); // p.double_load = 5
    }
  }

  /**
   * Labels FRAMESIZE tree node
   * @param p node to label
   */
  private static void label_FRAMESIZE(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: FRAMESIZE
    if(BURS.DEBUG) trace(p, 33, 10 + 0, p.getCost(2) /* r */);
    if (10 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(10));
      p.writePacked(0, 0xFFFE00FF, 0x400); // p.r = 4
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
    if(BURS.DEBUG) trace(p, 258, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 25, 0 + 0, p.getCost(9) /* any */);
    if (0 < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(0));
      p.writePacked(1, 0xFFFFF8FF, 0x300); // p.any = 3
    }
  }

  /**
   * Labels INT_CONSTANT tree node
   * @param p node to label
   */
  private static void label_INT_CONSTANT(AbstractBURS_TreeNode p) {
    p.initCost();
    // riv: INT_CONSTANT
    if(BURS.DEBUG) trace(p, 22, 0 + 0, p.getCost(7) /* riv */);
    if (0 < p.getCost(7) /* riv */) {
      p.setCost(7 /* riv */, (char)(0));
      p.writePacked(1, 0xFFFFFFCF, 0x20); // p.riv = 2
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
    if(BURS.DEBUG) trace(p, 23, 0 + 0, p.getCost(8) /* rlv */);
    if (0 < p.getCost(8) /* rlv */) {
      p.setCost(8 /* rlv */, (char)(0));
      p.writePacked(1, 0xFFFFFF3F, 0x80); // p.rlv = 2
    }
    // any: LONG_CONSTANT
    if(BURS.DEBUG) trace(p, 26, 0 + 0, p.getCost(9) /* any */);
    if (0 < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(0));
      p.writePacked(1, 0xFFFFF8FF, 0x400); // p.any = 4
    }
  }

  /**
   * Labels REGISTER tree node
   * @param p node to label
   */
  private static void label_REGISTER(AbstractBURS_TreeNode p) {
    p.initCost();
    // r: REGISTER
    if(BURS.DEBUG) trace(p, 21, 0 + 0, p.getCost(2) /* r */);
    if (0 < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(0));
      p.writePacked(0, 0xFFFE00FF, 0x100); // p.r = 1
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
    if(BURS.DEBUG) trace(p, 54, c + 0, p.getCost(9) /* any */);
    if (c < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(c));
      p.writePacked(1, 0xFFFFF8FF, 0x500); // p.any = 5
    }
  }

  /**
   * Labels NULL tree node
   * @param p node to label
   */
  private static void label_NULL(AbstractBURS_TreeNode p) {
    p.initCost();
    // any: NULL
    if(BURS.DEBUG) trace(p, 24, 0 + 0, p.getCost(9) /* any */);
    if (0 < p.getCost(9) /* any */) {
      p.setCost(9 /* any */, (char)(0));
      p.writePacked(1, 0xFFFFF8FF, 0x100); // p.any = 1
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
    if(BURS.DEBUG) trace(p, 391, c + 0, p.getCost(2) /* r */);
    if (c < p.getCost(2) /* r */) {
      p.setCost(2 /* r */, (char)(c));
      p.writePacked(0, 0xFFFE00FF, 0xEC00); // p.r = 236
      closure_r(p, c);
    }
    // float_load: MATERIALIZE_FP_CONSTANT(any)
    c = STATE(lchild).getCost(9 /* any */) + (Binary.getResult(P(p)).isFloat() ? 0 : INFINITE);
    if(BURS.DEBUG) trace(p, 392, c + 0, p.getCost(26) /* float_load */);
    if (c < p.getCost(26) /* float_load */) {
      p.setCost(26 /* float_load */, (char)(c));
      p.writePacked(2, 0xC7FFFFFF, 0x28000000); // p.float_load = 5
    }
    // double_load: MATERIALIZE_FP_CONSTANT(any)
    c = STATE(lchild).getCost(9 /* any */) + (Binary.getResult(P(p)).isDouble() ? 0 : INFINITE);
    if(BURS.DEBUG) trace(p, 393, c + 0, p.getCost(27) /* double_load */);
    if (c < p.getCost(27) /* double_load */) {
      p.setCost(27 /* double_load */, (char)(c));
      p.writePacked(3, 0xFFFFFFF8, 0x6); // p.double_load = 6
    }
  }

  /**
   * Labels CLEAR_FLOATING_POINT_STATE tree node
   * @param p node to label
   */
  private static void label_CLEAR_FLOATING_POINT_STATE(AbstractBURS_TreeNode p) {
    p.initCost();
    // stm: CLEAR_FLOATING_POINT_STATE
    if(BURS.DEBUG) trace(p, 53, 0 + 0, p.getCost(1) /* stm */);
    if (0 < p.getCost(1) /* stm */) {
      p.setCost(1 /* stm */, (char)(0));
      p.writePacked(0, 0xFFFFFF00, 0xD7); // p.stm = 215
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
    if(BURS.DEBUG) trace(p, 267, c + 0, p.getCost(1) /* stm */);
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
    if(BURS.DEBUG) trace(p, 47, 11 + 0, p.getCost(1) /* stm */);
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
      if(BURS.DEBUG) trace(p, 429, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3E00); // p.r = 62
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (VRL(p) == 0 && CMP_TO_TEST(CondMove.getCond(P(p))) ? (11 + 30):INFINITE);
      if(BURS.DEBUG) trace(p, 563, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x3F00); // p.r = 63
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
      if(BURS.DEBUG) trace(p, 305, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4000); // p.r = 64
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
      if(BURS.DEBUG) trace(p, 306, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4100); // p.r = 65
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
      if(BURS.DEBUG) trace(p, 307, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4200); // p.r = 66
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
      if(BURS.DEBUG) trace(p, 308, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4300); // p.r = 67
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(21 /* load8 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + FITS(CondMove.getVal2(P(p)), 8, (15 + 30));
      if(BURS.DEBUG) trace(p, 564, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4400); // p.r = 68
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(11 /* uload8 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 430, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4500); // p.r = 69
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(11 /* uload8 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 431, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4600); // p.r = 70
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(22 /* sload16 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + FITS(CondMove.getVal2(P(p)), 8, (15 + 30));
      if(BURS.DEBUG) trace(p, 565, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4700); // p.r = 71
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(10 /* load32 */) + STATE(rchild.getChild1()).getCost(7 /* riv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 432, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4800); // p.r = 72
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(7 /* riv */) + STATE(rchild.getChild1()).getCost(10 /* load32 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 433, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4900); // p.r = 73
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + STATE(rchild.getChild2()).getCost(9 /* any */) + ((VRL(p) == 0 && CondMove.getCond(P(p)).isNOT_EQUAL()) || (VRL(p) == 1 && CondMove.getCond(P(p)).isEQUAL()) ? 30 : INFINITE);
      if(BURS.DEBUG) trace(p, 566, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4A00); // p.r = 74
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(19 /* boolcmp */) + STATE(rchild.getChild2()).getCost(9 /* any */) + ((VRL(p) == 1 && CondMove.getCond(P(p)).isNOT_EQUAL()) || (VRL(p) == 0 && CondMove.getCond(P(p)).isEQUAL()) ? 30 : INFINITE);
      if(BURS.DEBUG) trace(p, 567, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4B00); // p.r = 75
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(18 /* bittest */) + STATE(rchild.getChild2()).getCost(9 /* any */) + ((VRL(p) == 0 || VRL(p) == 1) && EQ_NE(CondMove.getCond(P(p))) ? 30 : INFINITE);
      if(BURS.DEBUG) trace(p, 568, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4C00); // p.r = 76
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(4 /* cz */) + STATE(rchild.getChild2()).getCost(9 /* any */) + isZERO(VRL(p), 30);
      if(BURS.DEBUG) trace(p, 569, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4D00); // p.r = 77
        closure_r(p, c);
      }
    }
    if ( // r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(6 /* szp */) + STATE(rchild.getChild2()).getCost(9 /* any */) + isZERO(VRL(p), 30);
      if(BURS.DEBUG) trace(p, 570, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x4E00); // p.r = 78
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
      if(BURS.DEBUG) trace(p, 465, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xED00); // p.r = 237
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(26 /* float_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 466, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xEE00); // p.r = 238
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(27 /* double_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 467, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xEF00); // p.r = 239
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(26 /* float_load */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 468, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF000); // p.r = 240
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(27 /* double_load */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + 13+15;
      if(BURS.DEBUG) trace(p, 469, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF100); // p.r = 241
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
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (13 + 30);
      if(BURS.DEBUG) trace(p, 439, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7900); // p.r = 121
        closure_r(p, c);
      }
    }
    if ( // r: LCMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild1().getOpcode() == INT_CONSTANT_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (VRL(p) == 0 && CMP_TO_TEST(CondMove.getCond(P(p))) ? (11 + 30):INFINITE);
      if(BURS.DEBUG) trace(p, 571, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7A00); // p.r = 122
        closure_r(p, c);
      }
    }
    if ( // r: LCMP_CMOV(load64,OTHER_OPERAND(rlv,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(20 /* load64 */) + STATE(rchild.getChild1()).getCost(8 /* rlv */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 440, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7B00); // p.r = 123
        closure_r(p, c);
      }
    }
    if ( // r: LCMP_CMOV(rlv,OTHER_OPERAND(load64,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(8 /* rlv */) + STATE(rchild.getChild1()).getCost(20 /* load64 */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (15 + 30);
      if(BURS.DEBUG) trace(p, 441, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x7C00); // p.r = 124
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
      if(BURS.DEBUG) trace(p, 470, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF200); // p.r = 242
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(26 /* float_load */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 497, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF300); // p.r = 243
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild2()).getCost(27 /* double_load */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 498, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF400); // p.r = 244
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(26 /* float_load */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 499, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF500); // p.r = 245
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
      rchild.getOpcode() == OTHER_OPERAND_opcode && 
      rchild.getChild2().getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(2 /* r */) + STATE(rchild.getChild2().getChild1()).getCost(27 /* double_load */) + STATE(rchild.getChild2().getChild2()).getCost(2 /* r */) + 15+13*3;
      if(BURS.DEBUG) trace(p, 500, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF600); // p.r = 246
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(26 /* float_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (SSE2_CMP_OP(CondMove.getCond(P(p)), true) != null ? 15+13*3 : INFINITE);
      if(BURS.DEBUG) trace(p, 471, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF700); // p.r = 247
        closure_r(p, c);
      }
    }
    if ( // r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
      rchild.getOpcode() == OTHER_OPERAND_opcode  
    ) {
      c = STATE(lchild).getCost(2 /* r */) + STATE(rchild.getChild1()).getCost(27 /* double_load */) + STATE(rchild.getChild2()).getCost(9 /* any */) + (SSE2_CMP_OP(CondMove.getCond(P(p)), false) != null ? 15+13*3 : INFINITE);
      if(BURS.DEBUG) trace(p, 472, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF800); // p.r = 248
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
      if(BURS.DEBUG) trace(p, 648, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xF900); // p.r = 249
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
      if(BURS.DEBUG) trace(p, 649, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xFA00); // p.r = 250
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
      if(BURS.DEBUG) trace(p, 652, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xFB00); // p.r = 251
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
      if(BURS.DEBUG) trace(p, 653, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xFC00); // p.r = 252
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
      if(BURS.DEBUG) trace(p, 656, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xFD00); // p.r = 253
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
      if(BURS.DEBUG) trace(p, 657, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xFE00); // p.r = 254
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
      if(BURS.DEBUG) trace(p, 660, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0xFF00); // p.r = 255
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
      if(BURS.DEBUG) trace(p, 661, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10000); // p.r = 256
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
      if(BURS.DEBUG) trace(p, 650, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10100); // p.r = 257
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
      if(BURS.DEBUG) trace(p, 651, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10200); // p.r = 258
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
      if(BURS.DEBUG) trace(p, 654, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10300); // p.r = 259
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
      if(BURS.DEBUG) trace(p, 655, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10400); // p.r = 260
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
      if(BURS.DEBUG) trace(p, 658, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10500); // p.r = 261
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
      if(BURS.DEBUG) trace(p, 659, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10600); // p.r = 262
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
      if(BURS.DEBUG) trace(p, 662, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10700); // p.r = 263
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
      if(BURS.DEBUG) trace(p, 663, c + 0, p.getCost(2) /* r */);
      if (c < p.getCost(2) /* r */) {
        p.setCost(2 /* r */, (char)(c));
        p.writePacked(0, 0xFFFE00FF, 0x10800); // p.r = 264
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
      case 20: // load8_16_32_64: load8_16_32
      case 19: // load8_16_32_64: load64
      case 18: // load8_16_32: load8
      case 17: // load8_16_32: load16_32
      case 16: // load16_32: load32
      case 15: // load16_32: load16
      case 14: // load16: uload16
      case 13: // load16: sload16
      case 12: // load8: uload8
      case 11: // load8: sload8
      case 10: // address: address1scaledreg
      case 9: // address1scaledreg: address1reg
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
      case 53: // stm: CLEAR_FLOATING_POINT_STATE
      case 52: // r: GET_TIME_BASE
      case 51: // stm: RETURN(LONG_CONSTANT)
      case 50: // stm: RETURN(INT_CONSTANT)
      case 49: // stm: RETURN(NULL)
      case 48: // stm: ILLEGAL_INSTRUCTION
      case 47: // stm: PAUSE
      case 46: // stm: FENCE
      case 45: // stm: READ_CEILING
      case 44: // stm: WRITE_FLOOR
      case 43: // stm: GOTO
      case 42: // stm: TRAP
      case 41: // stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
      case 40: // stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
      case 39: // r: GET_CAUGHT_EXCEPTION
      case 38: // stm: IR_PROLOGUE
      case 37: // r: GUARD_COMBINE
      case 36: // r: GUARD_MOVE
      case 35: // stm: NOP
      case 34: // stm: RESOLVE
      case 33: // r: FRAMESIZE
      case 32: // stm: YIELDPOINT_BACKEDGE
      case 31: // stm: YIELDPOINT_EPILOGUE
      case 30: // stm: YIELDPOINT_PROLOGUE
      case 29: // stm: UNINT_END
      case 28: // stm: UNINT_BEGIN
      case 27: // stm: IG_PATCH_POINT
      case 26: // any: LONG_CONSTANT
      case 25: // any: ADDRESS_CONSTANT
      case 24: // any: NULL
      case 23: // rlv: LONG_CONSTANT
      case 22: // riv: INT_CONSTANT
      case 21: // r: REGISTER
        break;
      case 257: // stm: DOUBLE_IFCMP(double_load,r)
      case 256: // stm: DOUBLE_IFCMP(r,double_load)
      case 255: // stm: DOUBLE_IFCMP(r,r)
      case 254: // stm: FLOAT_IFCMP(float_load,r)
      case 253: // stm: FLOAT_IFCMP(r,float_load)
      case 252: // stm: FLOAT_IFCMP(r,r)
      case 251: // float_load: FLOAT_ALOAD(riv,riv)
      case 250: // r: FLOAT_ALOAD(rlv,rlv)
      case 249: // r: FLOAT_ALOAD(riv,r)
      case 248: // r: FLOAT_ALOAD(rlv,riv)
      case 247: // r: FLOAT_ALOAD(riv,riv)
      case 246: // float_load: FLOAT_ALOAD(rlv,riv)
      case 245: // float_load: FLOAT_LOAD(riv,riv)
      case 244: // r: FLOAT_LOAD(rlv,rlv)
      case 243: // r: FLOAT_LOAD(riv,riv)
      case 242: // double_load: DOUBLE_ALOAD(riv,riv)
      case 241: // double_load: DOUBLE_ALOAD(rlv,riv)
      case 240: // r: DOUBLE_ALOAD(rlv,rlv)
      case 239: // r: DOUBLE_ALOAD(riv,r)
      case 238: // double_load: DOUBLE_LOAD(rlv,rlv)
      case 237: // r: DOUBLE_ALOAD(rlv,riv)
      case 236: // r: DOUBLE_ALOAD(riv,riv)
      case 235: // double_load: DOUBLE_LOAD(riv,riv)
      case 234: // r: DOUBLE_LOAD(rlv,rlv)
      case 233: // r: DOUBLE_LOAD(riv,rlv)
      case 232: // r: DOUBLE_LOAD(riv,riv)
      case 231: // r: DOUBLE_REM(r,r)
      case 230: // r: FLOAT_REM(r,r)
      case 229: // r: DOUBLE_DIV(r,double_load)
      case 228: // r: DOUBLE_DIV(r,r)
      case 227: // r: FLOAT_DIV(r,float_load)
      case 226: // r: FLOAT_DIV(r,r)
      case 225: // r: DOUBLE_MUL(double_load,r)
      case 224: // r: DOUBLE_MUL(r,double_load)
      case 223: // r: DOUBLE_MUL(r,r)
      case 222: // r: FLOAT_MUL(float_load,r)
      case 221: // r: FLOAT_MUL(r,float_load)
      case 220: // r: FLOAT_MUL(r,r)
      case 219: // r: DOUBLE_SUB(r,double_load)
      case 218: // r: DOUBLE_SUB(r,r)
      case 217: // r: FLOAT_SUB(r,float_load)
      case 216: // r: FLOAT_SUB(r,r)
      case 215: // r: DOUBLE_ADD(double_load,r)
      case 214: // r: DOUBLE_ADD(r,double_load)
      case 213: // r: DOUBLE_ADD(r,r)
      case 212: // r: FLOAT_ADD(float_load,r)
      case 211: // r: FLOAT_ADD(r,float_load)
      case 210: // r: FLOAT_ADD(r,r)
      case 209: // szpr: LONG_XOR(load64,rlv)
      case 208: // szpr: LONG_XOR(r,load64)
      case 207: // szpr: LONG_XOR(r,rlv)
      case 206: // szpr: LONG_USHR(rlv,riv)
      case 205: // czr: LONG_SUB(load64,rlv)
      case 204: // czr: LONG_SUB(rlv,load64)
      case 203: // r: LONG_SUB(load64,r)
      case 202: // r: LONG_SUB(rlv,r)
      case 201: // czr: LONG_SUB(rlv,r)
      case 200: // szpr: LONG_SHR(rlv,riv)
      case 199: // szpr: LONG_SHL(rlv,riv)
      case 198: // r: LONG_REM(load64,rlv)
      case 197: // r: LONG_REM(rlv,load64)
      case 196: // r: LONG_REM(riv,rlv)
      case 195: // r: LONG_REM(rlv,riv)
      case 194: // r: LONG_REM(rlv,rlv)
      case 193: // szpr: LONG_OR(load64,rlv)
      case 192: // szpr: LONG_OR(r,load64)
      case 191: // szpr: LONG_OR(r,rlv)
      case 190: // r: INT_MUL(load64,rlv)
      case 189: // r: INT_MUL(r,load64)
      case 188: // r: LONG_MUL(r,rlv)
      case 187: // r: LONG_ALOAD(rlv,r)
      case 186: // r: LONG_ALOAD(rlv,riv)
      case 185: // r: LONG_LOAD(address1reg,address1scaledreg)
      case 184: // r: LONG_LOAD(address1scaledreg,address1reg)
      case 183: // r: LONG_LOAD(address1scaledreg,rlv)
      case 182: // r: LONG_LOAD(rlv,address1scaledreg)
      case 181: // r: LONG_LOAD(rlv,rlv)
      case 180: // stm: LONG_IFCMP(rlv,rlv)
      case 179: // r: LONG_DIV(load64,rlv)
      case 178: // r: LONG_DIV(rlv,load64)
      case 177: // r: LONG_DIV(riv,rlv)
      case 176: // r: LONG_DIV(rlv,riv)
      case 175: // r: LONG_DIV(rlv,rlv)
      case 174: // szp: LONG_AND(r,load8_16_32_64)
      case 173: // szp: LONG_AND(load8_16_32_64,rlv)
      case 172: // szpr: LONG_AND(load64,rlv)
      case 171: // szpr: LONG_AND(rlv,load64)
      case 170: // szp: LONG_AND(r,rlv)
      case 169: // szpr: LONG_AND(r,r)
      case 168: // szpr: LONG_AND(r,rlv)
      case 167: // czr: LONG_ADD(load64,rlv)
      case 166: // czr: LONG_ADD(rlv,load64)
      case 165: // r: LONG_ADD(r,rlv)
      case 164: // czr: LONG_ADD(r,r)
      case 163: // czr: LONG_ADD(r,riv)
      case 162: // czr: LONG_ADD(r,rlv)
      case 161: // load64: LONG_ALOAD(rlv,r)
      case 160: // load64: LONG_ALOAD(rlv,rlv)
      case 159: // load64: LONG_LOAD(rlv,rlv)
      case 158: // load32: INT_ALOAD(rlv,riv)
      case 157: // load32: INT_LOAD(rlv,rlv)
      case 156: // uload16: USHORT_ALOAD(rlv,riv)
      case 155: // r: USHORT_ALOAD(rlv,r)
      case 154: // r: USHORT_ALOAD(rlv,riv)
      case 153: // uload16: USHORT_LOAD(rlv,rlv)
      case 152: // r: USHORT_LOAD(rlv,rlv)
      case 151: // sload16: SHORT_ALOAD(rlv,riv)
      case 150: // r: SHORT_ALOAD(rlv,r)
      case 149: // r: SHORT_ALOAD(rlv,riv)
      case 148: // sload16: SHORT_LOAD(rlv,rlv)
      case 147: // r: SHORT_LOAD(rlv,rlv)
      case 146: // uload8: UBYTE_ALOAD(rlv,riv)
      case 145: // r: UBYTE_ALOAD(rlv,r)
      case 144: // r: UBYTE_ALOAD(rlv,riv)
      case 143: // uload8: UBYTE_LOAD(rlv,rlv)
      case 142: // r: UBYTE_LOAD(rlv,rlv)
      case 141: // sload8: BYTE_ALOAD(rlv,riv)
      case 140: // r: BYTE_ALOAD(rlv,r)
      case 139: // r: BYTE_ALOAD(rlv,riv)
      case 138: // sload8: BYTE_LOAD(rlv,rlv)
      case 137: // r: BYTE_LOAD(rlv,rlv)
      case 136: // r: LONG_ADD(address1reg,address1scaledreg)
      case 135: // r: LONG_ADD(address1scaledreg,address1reg)
      case 134: // r: LONG_ADD(r,address1scaledreg)
      case 133: // r: LONG_ADD(address1scaledreg,r)
      case 132: // szpr: INT_XOR(load32,riv)
      case 131: // szpr: INT_XOR(r,load32)
      case 130: // szpr: INT_XOR(r,riv)
      case 129: // szpr: INT_USHR(riv,riv)
      case 128: // czr: INT_SUB(load32,riv)
      case 127: // czr: INT_SUB(riv,load32)
      case 126: // r: INT_SUB(load32,r)
      case 125: // r: INT_SUB(riv,r)
      case 124: // czr: INT_SUB(riv,r)
      case 123: // szpr: INT_SHR(riv,riv)
      case 122: // szpr: INT_SHL(riv,riv)
      case 121: // r: UNSIGNED_REM_64_32(rlv,load32)
      case 120: // r: UNSIGNED_REM_64_32(rlv,riv)
      case 119: // r: INT_REM(riv,load32)
      case 118: // r: INT_REM(riv,riv)
      case 117: // szpr: INT_OR(load32,riv)
      case 116: // szpr: INT_OR(r,load32)
      case 115: // szpr: INT_OR(r,riv)
      case 114: // r: INT_MUL(load32,riv)
      case 113: // r: INT_MUL(r,load32)
      case 112: // r: INT_MUL(r,riv)
      case 111: // r: INT_ALOAD(rlv,riv)
      case 110: // r: INT_LOAD(address1reg,address1scaledreg)
      case 109: // r: INT_LOAD(address1scaledreg,address1reg)
      case 108: // r: INT_LOAD(address1scaledreg,rlv)
      case 107: // r: INT_LOAD(rlv,address1scaledreg)
      case 106: // r: INT_LOAD(rlv,rlv)
      case 105: // stm: INT_IFCMP2(riv,load32)
      case 104: // stm: INT_IFCMP2(load32,riv)
      case 103: // stm: INT_IFCMP2(r,riv)
      case 102: // stm: INT_IFCMP(r,load32)
      case 101: // stm: INT_IFCMP(load32,riv)
      case 100: // stm: INT_IFCMP(r,uload8)
      case 99: // stm: INT_IFCMP(uload8,r)
      case 98: // stm: INT_IFCMP(r,riv)
      case 97: // r: UNSIGNED_DIV_64_32(rlv,load32)
      case 96: // r: UNSIGNED_DIV_64_32(rlv,riv)
      case 95: // r: INT_DIV(riv,load32)
      case 94: // r: INT_DIV(riv,riv)
      case 93: // szp: INT_AND(r,load8_16_32)
      case 92: // szp: INT_AND(load8_16_32,riv)
      case 91: // szpr: INT_AND(load32,riv)
      case 90: // szpr: INT_AND(r,load32)
      case 89: // szp: INT_AND(r,riv)
      case 88: // szpr: INT_AND(r,riv)
      case 87: // czr: INT_ADD(load32,riv)
      case 86: // czr: INT_ADD(r,load32)
      case 85: // r: INT_ADD(r,riv)
      case 84: // czr: INT_ADD(r,riv)
      case 83: // boolcmp: BOOLEAN_CMP_LONG(rlv,load64)
      case 82: // r: BOOLEAN_CMP_LONG(r,load64)
      case 81: // boolcmp: BOOLEAN_CMP_LONG(load64,rlv)
      case 80: // r: BOOLEAN_CMP_LONG(load64,rlv)
      case 79: // boolcmp: BOOLEAN_CMP_LONG(r,rlv)
      case 78: // r: BOOLEAN_CMP_LONG(r,rlv)
      case 77: // boolcmp: BOOLEAN_CMP_INT(riv,load32)
      case 76: // r: BOOLEAN_CMP_INT(r,load32)
      case 75: // boolcmp: BOOLEAN_CMP_INT(load32,riv)
      case 74: // r: BOOLEAN_CMP_INT(load32,riv)
      case 73: // boolcmp: BOOLEAN_CMP_INT(r,riv)
      case 72: // r: BOOLEAN_CMP_INT(r,riv)
      case 71: // address: LONG_ADD(address1reg,address1scaledreg)
      case 70: // address: LONG_ADD(address1scaledreg,address1reg)
      case 69: // address: LONG_ADD(address1scaledreg,r)
      case 68: // address: LONG_ADD(r,address1scaledreg)
      case 67: // address: LONG_ADD(r,r)
      case 66: // address: INT_ADD(address1reg,address1scaledreg)
      case 65: // address: INT_ADD(address1scaledreg,address1reg)
      case 64: // address: INT_ADD(address1scaledreg,r)
      case 63: // address: INT_ADD(r,address1scaledreg)
      case 62: // address: INT_ADD(r,r)
      case 61: // stm: YIELDPOINT_OSR(any,any)
      case 60: // r: SYSCALL(r,any)
      case 59: // r: CALL(r,any)
      case 58: // r: LONG_CMP(rlv,rlv)
      case 57: // stm: TRAP_IF(riv,load32)
      case 56: // stm: TRAP_IF(load32,riv)
      case 55: // stm: TRAP_IF(r,r)
      case 54: // any: OTHER_OPERAND(any,any)
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2();
        }
        break;
      case 393: // double_load: MATERIALIZE_FP_CONSTANT(any)
      case 392: // float_load: MATERIALIZE_FP_CONSTANT(any)
      case 391: // r: MATERIALIZE_FP_CONSTANT(any)
      case 390: // double_load: LONG_BITS_AS_DOUBLE(load64)
      case 389: // r: LONG_BITS_AS_DOUBLE(rlv)
      case 388: // float_load: INT_BITS_AS_FLOAT(load32)
      case 387: // r: INT_BITS_AS_FLOAT(riv)
      case 386: // load64: DOUBLE_AS_LONG_BITS(double_load)
      case 385: // r: DOUBLE_AS_LONG_BITS(r)
      case 384: // load32: FLOAT_AS_INT_BITS(float_load)
      case 383: // r: FLOAT_AS_INT_BITS(r)
      case 382: // r: DOUBLE_2LONG(r)
      case 381: // r: DOUBLE_2INT(r)
      case 380: // r: FLOAT_2LONG(r)
      case 379: // r: FLOAT_2INT(r)
      case 378: // r: DOUBLE_2FLOAT(double_load)
      case 377: // r: DOUBLE_2FLOAT(r)
      case 376: // r: FLOAT_2DOUBLE(float_load)
      case 375: // r: FLOAT_2DOUBLE(r)
      case 374: // r: INT_2DOUBLE(load32)
      case 373: // r: INT_2DOUBLE(riv)
      case 372: // r: INT_2FLOAT(load32)
      case 371: // r: INT_2FLOAT(riv)
      case 370: // r: DOUBLE_MOVE(r)
      case 369: // r: FLOAT_MOVE(r)
      case 368: // r: LONG_2DOUBLE(r)
      case 367: // r: LONG_2FLOAT(r)
      case 366: // r: DOUBLE_SQRT(r)
      case 365: // r: FLOAT_SQRT(r)
      case 364: // r: DOUBLE_NEG(r)
      case 363: // r: FLOAT_NEG(r)
      case 362: // szpr: LONG_USHR(rlv,LONG_CONSTANT)
      case 361: // szpr: LONG_SHR(rlv,LONG_CONSTANT)
      case 360: // r: LONG_SHL(r,INT_CONSTANT)
      case 359: // szpr: LONG_SHL(r,INT_CONSTANT)
      case 358: // r: LONG_NOT(r)
      case 357: // szpr: LONG_NEG(r)
      case 356: // load64: LONG_MOVE(load64)
      case 355: // r: LONG_MOVE(riv)
      case 354: // r: LONG_MOVE(rlv)
      case 353: // r: LONG_LOAD(address,LONG_CONSTANT)
      case 352: // stm: LONG_IFCMP(r,LONG_CONSTANT)
      case 351: // load32: LONG_2INT(load64)
      case 350: // r: LONG_2INT(load64)
      case 349: // r: LONG_2INT(r)
      case 348: // r: LONG_MOVE(address)
      case 347: // r: LONG_ADD(address,LONG_CONSTANT)
      case 346: // szpr: INT_USHR(riv,INT_CONSTANT)
      case 345: // szpr: INT_SHR(riv,INT_CONSTANT)
      case 344: // r: INT_SHL(r,INT_CONSTANT)
      case 343: // szpr: INT_SHL(r,INT_CONSTANT)
      case 342: // r: INT_NOT(r)
      case 341: // szpr: INT_NEG(r)
      case 340: // load32: INT_MOVE(load32)
      case 339: // load16: INT_MOVE(load16)
      case 338: // uload16: INT_MOVE(uload16)
      case 337: // sload16: INT_MOVE(sload16)
      case 336: // load8: INT_MOVE(load8)
      case 335: // uload8: INT_MOVE(uload8)
      case 334: // sload8: INT_MOVE(sload8)
      case 333: // szp: INT_MOVE(szp)
      case 332: // szpr: INT_MOVE(szpr)
      case 331: // cz: INT_MOVE(cz)
      case 330: // czr: INT_MOVE(czr)
      case 329: // r: INT_MOVE(riv)
      case 328: // r: INT_LOAD(address,LONG_CONSTANT)
      case 327: // stm: INT_IFCMP(bittest,INT_CONSTANT)
      case 326: // stm: INT_IFCMP(szp,INT_CONSTANT)
      case 325: // stm: INT_IFCMP(cz,INT_CONSTANT)
      case 324: // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      case 323: // stm: INT_IFCMP(boolcmp,INT_CONSTANT)
      case 322: // stm: INT_IFCMP(sload16,INT_CONSTANT)
      case 321: // stm: INT_IFCMP(load8,INT_CONSTANT)
      case 320: // stm: INT_IFCMP(r,INT_CONSTANT)
      case 319: // r: INT_2USHORT(load16_32)
      case 318: // uload16: INT_2USHORT(load16_32)
      case 317: // szpr: INT_2USHORT(r)
      case 316: // sload16: INT_2SHORT(load16_32)
      case 315: // r: INT_2SHORT(load16_32)
      case 314: // r: INT_2SHORT(r)
      case 313: // r: INT_2ADDRZerExt(r)
      case 312: // r: INT_2LONG(load32)
      case 311: // r: INT_2LONG(r)
      case 310: // r: INT_2BYTE(load8_16_32)
      case 309: // r: INT_2BYTE(r)
      case 308: // r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 307: // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 306: // r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 305: // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
      case 304: // r: BOOLEAN_NOT(r)
      case 303: // r: BOOLEAN_CMP_LONG(cz,LONG_CONSTANT)
      case 302: // r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
      case 301: // r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      case 300: // r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
      case 299: // r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      case 298: // boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      case 297: // r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
      case 296: // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 295: // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 294: // boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 293: // r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
      case 292: // boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      case 291: // r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
      case 290: // boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      case 289: // r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
      case 288: // boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      case 287: // r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
      case 286: // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      case 285: // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 284: // r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
      case 283: // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 282: // boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 281: // r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
      case 280: // address: LONG_ADD(address1scaledreg,LONG_CONSTANT)
      case 279: // address1scaledreg: LONG_ADD(address1scaledreg,LONG_CONSTANT)
      case 278: // address1reg: LONG_ADD(address1reg,LONG_CONSTANT)
      case 277: // address1reg: LONG_MOVE(r)
      case 276: // address1reg: LONG_ADD(r,LONG_CONSTANT)
      case 275: // address1scaledreg: LONG_SHL(r,INT_CONSTANT)
      case 274: // address: INT_ADD(address1scaledreg,LONG_CONSTANT)
      case 273: // address1scaledreg: INT_ADD(address1scaledreg,LONG_CONSTANT)
      case 272: // address1reg: INT_ADD(address1reg,LONG_CONSTANT)
      case 271: // address1reg: INT_MOVE(r)
      case 270: // address1reg: INT_ADD(r,LONG_CONSTANT)
      case 269: // address1scaledreg: INT_SHL(r,INT_CONSTANT)
      case 268: // stm: RETURN(r)
      case 267: // stm: PREFETCH(r)
      case 266: // r: INT_AND(load16_32,INT_CONSTANT)
      case 265: // r: INT_2BYTE(load8_16_32)
      case 264: // r: INT_AND(load8_16_32,INT_CONSTANT)
      case 263: // uload8: INT_AND(load8_16_32,INT_CONSTANT)
      case 262: // stm: TRAP_IF(r,LONG_CONSTANT)
      case 261: // stm: TRAP_IF(r,INT_CONSTANT)
      case 260: // stm: SET_CAUGHT_EXCEPTION(r)
      case 259: // stm: NULL_CHECK(riv)
      case 258: // stm: LOWTABLESWITCH(r)
        if (kidnumber == 0) {
          return p.getChild1();
        }
        break;
      case 407: // szpr: LONG_SHL(LONG_SHR(r,INT_CONSTANT),INT_CONSTANT)
      case 406: // load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      case 405: // load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      case 404: // r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
      case 403: // r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
      case 402: // r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
      case 401: // r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
      case 400: // szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      case 399: // r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
      case 398: // r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
      case 397: // bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
      case 396: // bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
      case 395: // r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
      case 394: // r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        break;
      case 476: // stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
      case 475: // stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
      case 474: // stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
      case 473: // stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
      case 472: // r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
      case 471: // r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
      case 470: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
      case 469: // r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
      case 468: // r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
      case 467: // r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
      case 466: // r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
      case 465: // r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
      case 464: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
      case 463: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      case 462: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
      case 461: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
      case 460: // stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
      case 459: // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
      case 458: // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
      case 457: // stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
      case 456: // stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
      case 455: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
      case 454: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      case 453: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
      case 452: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
      case 451: // stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
      case 450: // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
      case 449: // stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
      case 448: // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
      case 447: // stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
      case 446: // stm: LONG_STORE(rlv,OTHER_OPERAND(address1reg,address1scaledreg))
      case 445: // stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,address1reg))
      case 444: // stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,rlv))
      case 443: // stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,address1scaledreg))
      case 442: // stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      case 441: // r: LCMP_CMOV(rlv,OTHER_OPERAND(load64,any))
      case 440: // r: LCMP_CMOV(load64,OTHER_OPERAND(rlv,any))
      case 439: // r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
      case 438: // stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
      case 437: // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
      case 436: // stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,rlv))
      case 435: // stm: INT_STORE(riv,OTHER_OPERAND(rlv,address1scaledreg))
      case 434: // stm: INT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      case 433: // r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
      case 432: // r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
      case 431: // r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
      case 430: // r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
      case 429: // r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
      case 428: // stm: BYTE_ASTORE(load8,OTHER_OPERAND(rlv,riv))
      case 427: // stm: BYTE_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      case 426: // stm: BYTE_STORE(load8,OTHER_OPERAND(rlv,rlv))
      case 425: // stm: BYTE_STORE(riv,OTHER_OPERAND(rlv,rlv))
      case 424: // stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
      case 423: // stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
      case 422: // stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
      case 421: // stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
      case 420: // stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
      case 419: // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
      case 418: // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
      case 417: // stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
      case 416: // stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
      case 415: // stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      case 414: // stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
      case 413: // stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
      case 412: // stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
      case 411: // stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
      case 410: // stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
      case 409: // stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
      case 408: // stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
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
      case 478: // stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
      case 477: // stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
        if (kidnumber == 0) {
          return p.getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2();
        }
        break;
      case 481: // r: SYSCALL(INT_CONSTANT,any)
      case 480: // r: CALL(INT_CONSTANT,any)
      case 479: // r: CALL(BRANCH_TARGET,any)
        if (kidnumber == 0) {
          return p.getChild2();
        }
        break;
      case 484: // r: SYSCALL(INT_LOAD(riv,riv),any)
      case 483: // r: CALL(LONG_LOAD(rlv,rlv),any)
      case 482: // r: CALL(INT_LOAD(riv,riv),any)
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
      case 500: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
      case 499: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
      case 498: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
      case 497: // r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
      case 496: // r: ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
      case 495: // r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv)))
      case 494: // r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv)))
      case 493: // r: ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
      case 492: // r: ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv)))
      case 491: // r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      case 490: // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
      case 489: // r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
      case 488: // r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
      case 487: // r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      case 486: // r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
      case 485: // r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
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
      case 502: // r: ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv)))
      case 501: // r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
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
      case 504: // r: ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv)))
      case 503: // r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
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
      case 524: // stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 523: // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 522: // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 521: // stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 520: // stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 519: // stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 518: // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 517: // stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 516: // stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 515: // stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 514: // stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 513: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 512: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 511: // stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 510: // stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 509: // stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 508: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 507: // stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 506: // stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 505: // stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
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
      case 528: // stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 527: // stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 526: // stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 525: // stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
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
      case 532: // stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 531: // stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
      case 530: // stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
      case 529: // stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
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
      case 536: // bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      case 535: // bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      case 534: // bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
      case 533: // bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild1().getChild2().getChild1();
        }
        break;
      case 538: // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
      case 537: // bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
        if (kidnumber == 0) {
          return p.getChild1().getChild2().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2();
        }
        break;
      case 540: // bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
      case 539: // bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2().getChild1();
        }
        break;
      case 562: // stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      case 561: // stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      case 560: // stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      case 559: // stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
      case 558: // stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 557: // stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 556: // stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 555: // stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 554: // stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 553: // stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 552: // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 551: // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 550: // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 549: // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 548: // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 547: // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
      case 546: // stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 545: // stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 544: // stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 543: // stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 542: // stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv,riv))
      case 541: // stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
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
      case 571: // r: LCMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
      case 570: // r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
      case 569: // r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
      case 568: // r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
      case 567: // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      case 566: // r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
      case 565: // r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
      case 564: // r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
      case 563: // r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild2();
        }
        break;
      case 579: // stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      case 578: // stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
      case 577: // stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      case 576: // stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
      case 575: // stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      case 574: // stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
      case 573: // stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
      case 572: // stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
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
      case 599: // stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 598: // stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 597: // stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 596: // stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 595: // stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 594: // stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 593: // stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 592: // stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 591: // stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 590: // stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
      case 589: // stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 588: // stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 587: // stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 586: // stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 585: // stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 584: // stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 583: // stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 582: // stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 581: // stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
      case 580: // stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
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
      case 619: // stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 618: // stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 617: // stm: LONG_ASTORE(LONG_SUB(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 616: // stm: LONG_STORE(LONG_SUB(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 615: // stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 614: // stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 613: // stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 612: // stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 611: // stm: LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 610: // stm: LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
      case 609: // stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 608: // stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 607: // stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 606: // stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 605: // stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 604: // stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 603: // stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 602: // stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 601: // stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
      case 600: // stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
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
      case 623: // r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      case 622: // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
      case 621: // r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
      case 620: // r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
        if (kidnumber == 0) {
          return p.getChild1().getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        break;
      case 625: // r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
      case 624: // r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
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
      case 627: // r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
      case 626: // r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
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
      case 635: // szpr: LONG_USHR(rlv,LONG_AND(r,LONG_CONSTANT))
      case 634: // stm: LONG_STORE(rlv,OTHER_OPERAND(address,LONG_CONSTANT))
      case 633: // szpr: LONG_SHR(rlv,INT_AND(r,LONG_CONSTANT))
      case 632: // szpr: LONG_SHL(rlv,INT_AND(r,INT_CONSTANT))
      case 631: // szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
      case 630: // stm: INT_STORE(riv,OTHER_OPERAND(address,LONG_CONSTANT))
      case 629: // szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
      case 628: // szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
        if (kidnumber == 0) {
          return p.getChild1();
        }
        if (kidnumber == 1) {
          return p.getChild2().getChild1();
        }
        break;
      case 647: // stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 646: // stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 645: // stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 644: // stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 643: // stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 642: // stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 641: // stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 640: // stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 639: // stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 638: // stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 637: // stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
      case 636: // stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
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
      case 651: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 650: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 649: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
      case 648: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
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
      case 655: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 654: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 653: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
      case 652: // r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
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
      case 659: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 658: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
      case 657: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
      case 656: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
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
      case 663: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 662: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
      case 661: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
      case 660: // r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
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
    // 20: load8_16_32_64: load8_16_32
    // 19: load8_16_32_64: load64
    // 18: load8_16_32: load8
    // 17: load8_16_32: load16_32
    // 16: load16_32: load32
    // 15: load16_32: load16
    // 14: load16: uload16
    // 13: load16: sload16
    // 12: load8: uload8
    // 11: load8: sload8
    // 10: address: address1scaledreg
    // 9: address1scaledreg: address1reg
    // 8: any: riv
    // 7: rlv: r
    // 6: riv: r
    // 5: szp: szpr
    // 4: r: szpr
    // 3: cz: czr
    // 2: r: czr
    // 1: stm: r
    if (eruleno <= 20) {
      if (VM.VerifyAssertions) VM._assert(eruleno > 0);
      mark(p, ntsrule[0]);
    }
    // 53: stm: CLEAR_FLOATING_POINT_STATE
    // 52: r: GET_TIME_BASE
    // 51: stm: RETURN(LONG_CONSTANT)
    // 50: stm: RETURN(INT_CONSTANT)
    // 49: stm: RETURN(NULL)
    // 48: stm: ILLEGAL_INSTRUCTION
    // 47: stm: PAUSE
    // 46: stm: FENCE
    // 45: stm: READ_CEILING
    // 44: stm: WRITE_FLOOR
    // 43: stm: GOTO
    // 42: stm: TRAP
    // 41: stm: SET_CAUGHT_EXCEPTION(LONG_CONSTANT)
    // 40: stm: SET_CAUGHT_EXCEPTION(INT_CONSTANT)
    // 39: r: GET_CAUGHT_EXCEPTION
    // 38: stm: IR_PROLOGUE
    // 37: r: GUARD_COMBINE
    // 36: r: GUARD_MOVE
    // 35: stm: NOP
    // 34: stm: RESOLVE
    // 33: r: FRAMESIZE
    // 32: stm: YIELDPOINT_BACKEDGE
    // 31: stm: YIELDPOINT_EPILOGUE
    // 30: stm: YIELDPOINT_PROLOGUE
    // 29: stm: UNINT_END
    // 28: stm: UNINT_BEGIN
    // 27: stm: IG_PATCH_POINT
    // 26: any: LONG_CONSTANT
    // 25: any: ADDRESS_CONSTANT
    // 24: any: NULL
    // 23: rlv: LONG_CONSTANT
    // 22: riv: INT_CONSTANT
    // 21: r: REGISTER
    else if (eruleno <= 53) {
    }
    // 257: stm: DOUBLE_IFCMP(double_load,r)
    // 256: stm: DOUBLE_IFCMP(r,double_load)
    // 255: stm: DOUBLE_IFCMP(r,r)
    // 254: stm: FLOAT_IFCMP(float_load,r)
    // 253: stm: FLOAT_IFCMP(r,float_load)
    // 252: stm: FLOAT_IFCMP(r,r)
    // 251: float_load: FLOAT_ALOAD(riv,riv)
    // 250: r: FLOAT_ALOAD(rlv,rlv)
    // 249: r: FLOAT_ALOAD(riv,r)
    // 248: r: FLOAT_ALOAD(rlv,riv)
    // 247: r: FLOAT_ALOAD(riv,riv)
    // 246: float_load: FLOAT_ALOAD(rlv,riv)
    // 245: float_load: FLOAT_LOAD(riv,riv)
    // 244: r: FLOAT_LOAD(rlv,rlv)
    // 243: r: FLOAT_LOAD(riv,riv)
    // 242: double_load: DOUBLE_ALOAD(riv,riv)
    // 241: double_load: DOUBLE_ALOAD(rlv,riv)
    // 240: r: DOUBLE_ALOAD(rlv,rlv)
    // 239: r: DOUBLE_ALOAD(riv,r)
    // 238: double_load: DOUBLE_LOAD(rlv,rlv)
    // 237: r: DOUBLE_ALOAD(rlv,riv)
    // 236: r: DOUBLE_ALOAD(riv,riv)
    // 235: double_load: DOUBLE_LOAD(riv,riv)
    // 234: r: DOUBLE_LOAD(rlv,rlv)
    // 233: r: DOUBLE_LOAD(riv,rlv)
    // 232: r: DOUBLE_LOAD(riv,riv)
    // 231: r: DOUBLE_REM(r,r)
    // 230: r: FLOAT_REM(r,r)
    // 229: r: DOUBLE_DIV(r,double_load)
    // 228: r: DOUBLE_DIV(r,r)
    // 227: r: FLOAT_DIV(r,float_load)
    // 226: r: FLOAT_DIV(r,r)
    // 225: r: DOUBLE_MUL(double_load,r)
    // 224: r: DOUBLE_MUL(r,double_load)
    // 223: r: DOUBLE_MUL(r,r)
    // 222: r: FLOAT_MUL(float_load,r)
    // 221: r: FLOAT_MUL(r,float_load)
    // 220: r: FLOAT_MUL(r,r)
    // 219: r: DOUBLE_SUB(r,double_load)
    // 218: r: DOUBLE_SUB(r,r)
    // 217: r: FLOAT_SUB(r,float_load)
    // 216: r: FLOAT_SUB(r,r)
    // 215: r: DOUBLE_ADD(double_load,r)
    // 214: r: DOUBLE_ADD(r,double_load)
    // 213: r: DOUBLE_ADD(r,r)
    // 212: r: FLOAT_ADD(float_load,r)
    // 211: r: FLOAT_ADD(r,float_load)
    // 210: r: FLOAT_ADD(r,r)
    // 209: szpr: LONG_XOR(load64,rlv)
    // 208: szpr: LONG_XOR(r,load64)
    // 207: szpr: LONG_XOR(r,rlv)
    // 206: szpr: LONG_USHR(rlv,riv)
    // 205: czr: LONG_SUB(load64,rlv)
    // 204: czr: LONG_SUB(rlv,load64)
    // 203: r: LONG_SUB(load64,r)
    // 202: r: LONG_SUB(rlv,r)
    // 201: czr: LONG_SUB(rlv,r)
    // 200: szpr: LONG_SHR(rlv,riv)
    // 199: szpr: LONG_SHL(rlv,riv)
    // 198: r: LONG_REM(load64,rlv)
    // 197: r: LONG_REM(rlv,load64)
    // 196: r: LONG_REM(riv,rlv)
    // 195: r: LONG_REM(rlv,riv)
    // 194: r: LONG_REM(rlv,rlv)
    // 193: szpr: LONG_OR(load64,rlv)
    // 192: szpr: LONG_OR(r,load64)
    // 191: szpr: LONG_OR(r,rlv)
    // 190: r: INT_MUL(load64,rlv)
    // 189: r: INT_MUL(r,load64)
    // 188: r: LONG_MUL(r,rlv)
    // 187: r: LONG_ALOAD(rlv,r)
    // 186: r: LONG_ALOAD(rlv,riv)
    // 185: r: LONG_LOAD(address1reg,address1scaledreg)
    // 184: r: LONG_LOAD(address1scaledreg,address1reg)
    // 183: r: LONG_LOAD(address1scaledreg,rlv)
    // 182: r: LONG_LOAD(rlv,address1scaledreg)
    // 181: r: LONG_LOAD(rlv,rlv)
    // 180: stm: LONG_IFCMP(rlv,rlv)
    // 179: r: LONG_DIV(load64,rlv)
    // 178: r: LONG_DIV(rlv,load64)
    // 177: r: LONG_DIV(riv,rlv)
    // 176: r: LONG_DIV(rlv,riv)
    // 175: r: LONG_DIV(rlv,rlv)
    // 174: szp: LONG_AND(r,load8_16_32_64)
    // 173: szp: LONG_AND(load8_16_32_64,rlv)
    // 172: szpr: LONG_AND(load64,rlv)
    // 171: szpr: LONG_AND(rlv,load64)
    // 170: szp: LONG_AND(r,rlv)
    // 169: szpr: LONG_AND(r,r)
    // 168: szpr: LONG_AND(r,rlv)
    // 167: czr: LONG_ADD(load64,rlv)
    // 166: czr: LONG_ADD(rlv,load64)
    // 165: r: LONG_ADD(r,rlv)
    // 164: czr: LONG_ADD(r,r)
    // 163: czr: LONG_ADD(r,riv)
    // 162: czr: LONG_ADD(r,rlv)
    // 161: load64: LONG_ALOAD(rlv,r)
    // 160: load64: LONG_ALOAD(rlv,rlv)
    // 159: load64: LONG_LOAD(rlv,rlv)
    // 158: load32: INT_ALOAD(rlv,riv)
    // 157: load32: INT_LOAD(rlv,rlv)
    // 156: uload16: USHORT_ALOAD(rlv,riv)
    // 155: r: USHORT_ALOAD(rlv,r)
    // 154: r: USHORT_ALOAD(rlv,riv)
    // 153: uload16: USHORT_LOAD(rlv,rlv)
    // 152: r: USHORT_LOAD(rlv,rlv)
    // 151: sload16: SHORT_ALOAD(rlv,riv)
    // 150: r: SHORT_ALOAD(rlv,r)
    // 149: r: SHORT_ALOAD(rlv,riv)
    // 148: sload16: SHORT_LOAD(rlv,rlv)
    // 147: r: SHORT_LOAD(rlv,rlv)
    // 146: uload8: UBYTE_ALOAD(rlv,riv)
    // 145: r: UBYTE_ALOAD(rlv,r)
    // 144: r: UBYTE_ALOAD(rlv,riv)
    // 143: uload8: UBYTE_LOAD(rlv,rlv)
    // 142: r: UBYTE_LOAD(rlv,rlv)
    // 141: sload8: BYTE_ALOAD(rlv,riv)
    // 140: r: BYTE_ALOAD(rlv,r)
    // 139: r: BYTE_ALOAD(rlv,riv)
    // 138: sload8: BYTE_LOAD(rlv,rlv)
    // 137: r: BYTE_LOAD(rlv,rlv)
    // 136: r: LONG_ADD(address1reg,address1scaledreg)
    // 135: r: LONG_ADD(address1scaledreg,address1reg)
    // 134: r: LONG_ADD(r,address1scaledreg)
    // 133: r: LONG_ADD(address1scaledreg,r)
    // 132: szpr: INT_XOR(load32,riv)
    // 131: szpr: INT_XOR(r,load32)
    // 130: szpr: INT_XOR(r,riv)
    // 129: szpr: INT_USHR(riv,riv)
    // 128: czr: INT_SUB(load32,riv)
    // 127: czr: INT_SUB(riv,load32)
    // 126: r: INT_SUB(load32,r)
    // 125: r: INT_SUB(riv,r)
    // 124: czr: INT_SUB(riv,r)
    // 123: szpr: INT_SHR(riv,riv)
    // 122: szpr: INT_SHL(riv,riv)
    // 121: r: UNSIGNED_REM_64_32(rlv,load32)
    // 120: r: UNSIGNED_REM_64_32(rlv,riv)
    // 119: r: INT_REM(riv,load32)
    // 118: r: INT_REM(riv,riv)
    // 117: szpr: INT_OR(load32,riv)
    // 116: szpr: INT_OR(r,load32)
    // 115: szpr: INT_OR(r,riv)
    // 114: r: INT_MUL(load32,riv)
    // 113: r: INT_MUL(r,load32)
    // 112: r: INT_MUL(r,riv)
    // 111: r: INT_ALOAD(rlv,riv)
    // 110: r: INT_LOAD(address1reg,address1scaledreg)
    // 109: r: INT_LOAD(address1scaledreg,address1reg)
    // 108: r: INT_LOAD(address1scaledreg,rlv)
    // 107: r: INT_LOAD(rlv,address1scaledreg)
    // 106: r: INT_LOAD(rlv,rlv)
    // 105: stm: INT_IFCMP2(riv,load32)
    // 104: stm: INT_IFCMP2(load32,riv)
    // 103: stm: INT_IFCMP2(r,riv)
    // 102: stm: INT_IFCMP(r,load32)
    // 101: stm: INT_IFCMP(load32,riv)
    // 100: stm: INT_IFCMP(r,uload8)
    // 99: stm: INT_IFCMP(uload8,r)
    // 98: stm: INT_IFCMP(r,riv)
    // 97: r: UNSIGNED_DIV_64_32(rlv,load32)
    // 96: r: UNSIGNED_DIV_64_32(rlv,riv)
    // 95: r: INT_DIV(riv,load32)
    // 94: r: INT_DIV(riv,riv)
    // 93: szp: INT_AND(r,load8_16_32)
    // 92: szp: INT_AND(load8_16_32,riv)
    // 91: szpr: INT_AND(load32,riv)
    // 90: szpr: INT_AND(r,load32)
    // 89: szp: INT_AND(r,riv)
    // 88: szpr: INT_AND(r,riv)
    // 87: czr: INT_ADD(load32,riv)
    // 86: czr: INT_ADD(r,load32)
    // 85: r: INT_ADD(r,riv)
    // 84: czr: INT_ADD(r,riv)
    // 83: boolcmp: BOOLEAN_CMP_LONG(rlv,load64)
    // 82: r: BOOLEAN_CMP_LONG(r,load64)
    // 81: boolcmp: BOOLEAN_CMP_LONG(load64,rlv)
    // 80: r: BOOLEAN_CMP_LONG(load64,rlv)
    // 79: boolcmp: BOOLEAN_CMP_LONG(r,rlv)
    // 78: r: BOOLEAN_CMP_LONG(r,rlv)
    // 77: boolcmp: BOOLEAN_CMP_INT(riv,load32)
    // 76: r: BOOLEAN_CMP_INT(r,load32)
    // 75: boolcmp: BOOLEAN_CMP_INT(load32,riv)
    // 74: r: BOOLEAN_CMP_INT(load32,riv)
    // 73: boolcmp: BOOLEAN_CMP_INT(r,riv)
    // 72: r: BOOLEAN_CMP_INT(r,riv)
    // 71: address: LONG_ADD(address1reg,address1scaledreg)
    // 70: address: LONG_ADD(address1scaledreg,address1reg)
    // 69: address: LONG_ADD(address1scaledreg,r)
    // 68: address: LONG_ADD(r,address1scaledreg)
    // 67: address: LONG_ADD(r,r)
    // 66: address: INT_ADD(address1reg,address1scaledreg)
    // 65: address: INT_ADD(address1scaledreg,address1reg)
    // 64: address: INT_ADD(address1scaledreg,r)
    // 63: address: INT_ADD(r,address1scaledreg)
    // 62: address: INT_ADD(r,r)
    // 61: stm: YIELDPOINT_OSR(any,any)
    // 60: r: SYSCALL(r,any)
    // 59: r: CALL(r,any)
    // 58: r: LONG_CMP(rlv,rlv)
    // 57: stm: TRAP_IF(riv,load32)
    // 56: stm: TRAP_IF(load32,riv)
    // 55: stm: TRAP_IF(r,r)
    // 54: any: OTHER_OPERAND(any,any)
    else if (eruleno <= 257) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2(), ntsrule[1]);
    }
    // 393: double_load: MATERIALIZE_FP_CONSTANT(any)
    // 392: float_load: MATERIALIZE_FP_CONSTANT(any)
    // 391: r: MATERIALIZE_FP_CONSTANT(any)
    // 390: double_load: LONG_BITS_AS_DOUBLE(load64)
    // 389: r: LONG_BITS_AS_DOUBLE(rlv)
    // 388: float_load: INT_BITS_AS_FLOAT(load32)
    // 387: r: INT_BITS_AS_FLOAT(riv)
    // 386: load64: DOUBLE_AS_LONG_BITS(double_load)
    // 385: r: DOUBLE_AS_LONG_BITS(r)
    // 384: load32: FLOAT_AS_INT_BITS(float_load)
    // 383: r: FLOAT_AS_INT_BITS(r)
    // 382: r: DOUBLE_2LONG(r)
    // 381: r: DOUBLE_2INT(r)
    // 380: r: FLOAT_2LONG(r)
    // 379: r: FLOAT_2INT(r)
    // 378: r: DOUBLE_2FLOAT(double_load)
    // 377: r: DOUBLE_2FLOAT(r)
    // 376: r: FLOAT_2DOUBLE(float_load)
    // 375: r: FLOAT_2DOUBLE(r)
    // 374: r: INT_2DOUBLE(load32)
    // 373: r: INT_2DOUBLE(riv)
    // 372: r: INT_2FLOAT(load32)
    // 371: r: INT_2FLOAT(riv)
    // 370: r: DOUBLE_MOVE(r)
    // 369: r: FLOAT_MOVE(r)
    // 368: r: LONG_2DOUBLE(r)
    // 367: r: LONG_2FLOAT(r)
    // 366: r: DOUBLE_SQRT(r)
    // 365: r: FLOAT_SQRT(r)
    // 364: r: DOUBLE_NEG(r)
    // 363: r: FLOAT_NEG(r)
    // 362: szpr: LONG_USHR(rlv,LONG_CONSTANT)
    // 361: szpr: LONG_SHR(rlv,LONG_CONSTANT)
    // 360: r: LONG_SHL(r,INT_CONSTANT)
    // 359: szpr: LONG_SHL(r,INT_CONSTANT)
    // 358: r: LONG_NOT(r)
    // 357: szpr: LONG_NEG(r)
    // 356: load64: LONG_MOVE(load64)
    // 355: r: LONG_MOVE(riv)
    // 354: r: LONG_MOVE(rlv)
    // 353: r: LONG_LOAD(address,LONG_CONSTANT)
    // 352: stm: LONG_IFCMP(r,LONG_CONSTANT)
    // 351: load32: LONG_2INT(load64)
    // 350: r: LONG_2INT(load64)
    // 349: r: LONG_2INT(r)
    // 348: r: LONG_MOVE(address)
    // 347: r: LONG_ADD(address,LONG_CONSTANT)
    // 346: szpr: INT_USHR(riv,INT_CONSTANT)
    // 345: szpr: INT_SHR(riv,INT_CONSTANT)
    // 344: r: INT_SHL(r,INT_CONSTANT)
    // 343: szpr: INT_SHL(r,INT_CONSTANT)
    // 342: r: INT_NOT(r)
    // 341: szpr: INT_NEG(r)
    // 340: load32: INT_MOVE(load32)
    // 339: load16: INT_MOVE(load16)
    // 338: uload16: INT_MOVE(uload16)
    // 337: sload16: INT_MOVE(sload16)
    // 336: load8: INT_MOVE(load8)
    // 335: uload8: INT_MOVE(uload8)
    // 334: sload8: INT_MOVE(sload8)
    // 333: szp: INT_MOVE(szp)
    // 332: szpr: INT_MOVE(szpr)
    // 331: cz: INT_MOVE(cz)
    // 330: czr: INT_MOVE(czr)
    // 329: r: INT_MOVE(riv)
    // 328: r: INT_LOAD(address,LONG_CONSTANT)
    // 327: stm: INT_IFCMP(bittest,INT_CONSTANT)
    // 326: stm: INT_IFCMP(szp,INT_CONSTANT)
    // 325: stm: INT_IFCMP(cz,INT_CONSTANT)
    // 324: stm: INT_IFCMP(boolcmp,INT_CONSTANT)
    // 323: stm: INT_IFCMP(boolcmp,INT_CONSTANT)
    // 322: stm: INT_IFCMP(sload16,INT_CONSTANT)
    // 321: stm: INT_IFCMP(load8,INT_CONSTANT)
    // 320: stm: INT_IFCMP(r,INT_CONSTANT)
    // 319: r: INT_2USHORT(load16_32)
    // 318: uload16: INT_2USHORT(load16_32)
    // 317: szpr: INT_2USHORT(r)
    // 316: sload16: INT_2SHORT(load16_32)
    // 315: r: INT_2SHORT(load16_32)
    // 314: r: INT_2SHORT(r)
    // 313: r: INT_2ADDRZerExt(r)
    // 312: r: INT_2LONG(load32)
    // 311: r: INT_2LONG(r)
    // 310: r: INT_2BYTE(load8_16_32)
    // 309: r: INT_2BYTE(r)
    // 308: r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 307: r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 306: r: CMP_CMOV(load32,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 305: r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(INT_CONSTANT,INT_CONSTANT)))
    // 304: r: BOOLEAN_NOT(r)
    // 303: r: BOOLEAN_CMP_LONG(cz,LONG_CONSTANT)
    // 302: r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
    // 301: r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    // 300: r: BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
    // 299: r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    // 298: boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    // 297: r: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    // 296: boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 295: r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 294: boolcmp: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 293: r: BOOLEAN_CMP_INT(boolcmp,INT_CONSTANT)
    // 292: boolcmp: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
    // 291: r: BOOLEAN_CMP_INT(bittest,INT_CONSTANT)
    // 290: boolcmp: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
    // 289: r: BOOLEAN_CMP_INT(szp,INT_CONSTANT)
    // 288: boolcmp: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
    // 287: r: BOOLEAN_CMP_INT(cz,INT_CONSTANT)
    // 286: r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    // 285: r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 284: r: BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    // 283: r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 282: boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 281: r: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    // 280: address: LONG_ADD(address1scaledreg,LONG_CONSTANT)
    // 279: address1scaledreg: LONG_ADD(address1scaledreg,LONG_CONSTANT)
    // 278: address1reg: LONG_ADD(address1reg,LONG_CONSTANT)
    // 277: address1reg: LONG_MOVE(r)
    // 276: address1reg: LONG_ADD(r,LONG_CONSTANT)
    // 275: address1scaledreg: LONG_SHL(r,INT_CONSTANT)
    // 274: address: INT_ADD(address1scaledreg,LONG_CONSTANT)
    // 273: address1scaledreg: INT_ADD(address1scaledreg,LONG_CONSTANT)
    // 272: address1reg: INT_ADD(address1reg,LONG_CONSTANT)
    // 271: address1reg: INT_MOVE(r)
    // 270: address1reg: INT_ADD(r,LONG_CONSTANT)
    // 269: address1scaledreg: INT_SHL(r,INT_CONSTANT)
    // 268: stm: RETURN(r)
    // 267: stm: PREFETCH(r)
    // 266: r: INT_AND(load16_32,INT_CONSTANT)
    // 265: r: INT_2BYTE(load8_16_32)
    // 264: r: INT_AND(load8_16_32,INT_CONSTANT)
    // 263: uload8: INT_AND(load8_16_32,INT_CONSTANT)
    // 262: stm: TRAP_IF(r,LONG_CONSTANT)
    // 261: stm: TRAP_IF(r,INT_CONSTANT)
    // 260: stm: SET_CAUGHT_EXCEPTION(r)
    // 259: stm: NULL_CHECK(riv)
    // 258: stm: LOWTABLESWITCH(r)
    else if (eruleno <= 393) {
      mark(p.getChild1(), ntsrule[0]);
    }
    // 407: szpr: LONG_SHL(LONG_SHR(r,INT_CONSTANT),INT_CONSTANT)
    // 406: load32: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
    // 405: load32: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
    // 404: r: LONG_2INT(LONG_SHR(load64,INT_CONSTANT))
    // 403: r: LONG_2INT(LONG_USHR(load64,INT_CONSTANT))
    // 402: r: LONG_2INT(LONG_SHR(r,INT_CONSTANT))
    // 401: r: LONG_2INT(LONG_USHR(r,INT_CONSTANT))
    // 400: szpr: INT_SHL(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
    // 399: r: LONG_AND(INT_2LONG(load32),LONG_CONSTANT)
    // 398: r: LONG_AND(INT_2LONG(r),LONG_CONSTANT)
    // 397: bittest: INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
    // 396: bittest: INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
    // 395: r: INT_USHR(INT_SHL(load16_32,INT_CONSTANT),INT_CONSTANT)
    // 394: r: INT_USHR(INT_SHL(load8_16_32,INT_CONSTANT),INT_CONSTANT)
    else if (eruleno <= 407) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
    }
    // 476: stm: LONG_STORE(load64,OTHER_OPERAND(rlv,riv))
    // 475: stm: LONG_STORE(load64,OTHER_OPERAND(riv,riv))
    // 474: stm: LONG_ASTORE(load64,OTHER_OPERAND(rlv,riv))
    // 473: stm: LONG_ASTORE(load64,OTHER_OPERAND(riv,riv))
    // 472: r: FCMP_FCMOV(r,OTHER_OPERAND(double_load,any))
    // 471: r: FCMP_FCMOV(r,OTHER_OPERAND(float_load,any))
    // 470: r: FCMP_FCMOV(r,OTHER_OPERAND(r,any))
    // 469: r: FCMP_CMOV(double_load,OTHER_OPERAND(r,any))
    // 468: r: FCMP_CMOV(float_load,OTHER_OPERAND(r,any))
    // 467: r: FCMP_CMOV(r,OTHER_OPERAND(double_load,any))
    // 466: r: FCMP_CMOV(r,OTHER_OPERAND(float_load,any))
    // 465: r: FCMP_CMOV(r,OTHER_OPERAND(r,any))
    // 464: stm: FLOAT_ASTORE(r,OTHER_OPERAND(r,r))
    // 463: stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,rlv))
    // 462: stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,rlv))
    // 461: stm: FLOAT_ASTORE(r,OTHER_OPERAND(rlv,riv))
    // 460: stm: FLOAT_ASTORE(r,OTHER_OPERAND(riv,riv))
    // 459: stm: FLOAT_STORE(r,OTHER_OPERAND(riv,rlv))
    // 458: stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,riv))
    // 457: stm: FLOAT_STORE(r,OTHER_OPERAND(rlv,rlv))
    // 456: stm: FLOAT_STORE(r,OTHER_OPERAND(riv,riv))
    // 455: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(r,r))
    // 454: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,rlv))
    // 453: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,rlv))
    // 452: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(rlv,riv))
    // 451: stm: DOUBLE_ASTORE(r,OTHER_OPERAND(riv,riv))
    // 450: stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,rlv))
    // 449: stm: DOUBLE_STORE(r,OTHER_OPERAND(rlv,riv))
    // 448: stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,rlv))
    // 447: stm: DOUBLE_STORE(r,OTHER_OPERAND(riv,riv))
    // 446: stm: LONG_STORE(rlv,OTHER_OPERAND(address1reg,address1scaledreg))
    // 445: stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,address1reg))
    // 444: stm: LONG_STORE(rlv,OTHER_OPERAND(address1scaledreg,rlv))
    // 443: stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,address1scaledreg))
    // 442: stm: LONG_STORE(rlv,OTHER_OPERAND(rlv,rlv))
    // 441: r: LCMP_CMOV(rlv,OTHER_OPERAND(load64,any))
    // 440: r: LCMP_CMOV(load64,OTHER_OPERAND(rlv,any))
    // 439: r: LCMP_CMOV(r,OTHER_OPERAND(rlv,any))
    // 438: stm: INT_STORE(riv,OTHER_OPERAND(address1reg,address1scaledreg))
    // 437: stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,address1reg))
    // 436: stm: INT_STORE(riv,OTHER_OPERAND(address1scaledreg,rlv))
    // 435: stm: INT_STORE(riv,OTHER_OPERAND(rlv,address1scaledreg))
    // 434: stm: INT_STORE(riv,OTHER_OPERAND(rlv,rlv))
    // 433: r: CMP_CMOV(riv,OTHER_OPERAND(load32,any))
    // 432: r: CMP_CMOV(load32,OTHER_OPERAND(riv,any))
    // 431: r: CMP_CMOV(riv,OTHER_OPERAND(uload8,any))
    // 430: r: CMP_CMOV(uload8,OTHER_OPERAND(riv,any))
    // 429: r: CMP_CMOV(r,OTHER_OPERAND(riv,any))
    // 428: stm: BYTE_ASTORE(load8,OTHER_OPERAND(rlv,riv))
    // 427: stm: BYTE_ASTORE(riv,OTHER_OPERAND(rlv,riv))
    // 426: stm: BYTE_STORE(load8,OTHER_OPERAND(rlv,rlv))
    // 425: stm: BYTE_STORE(riv,OTHER_OPERAND(rlv,rlv))
    // 424: stm: BYTE_ASTORE(boolcmp,OTHER_OPERAND(riv,riv))
    // 423: stm: BYTE_STORE(boolcmp,OTHER_OPERAND(riv,riv))
    // 422: stm: LONG_ASTORE(r,OTHER_OPERAND(r,r))
    // 421: stm: LONG_ASTORE(r,OTHER_OPERAND(rlv,rlv))
    // 420: stm: LONG_ASTORE(r,OTHER_OPERAND(riv,riv))
    // 419: stm: INT_ASTORE(riv,OTHER_OPERAND(riv,rlv))
    // 418: stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,riv))
    // 417: stm: INT_ASTORE(riv,OTHER_OPERAND(rlv,rlv))
    // 416: stm: INT_ASTORE(riv,OTHER_OPERAND(r,r))
    // 415: stm: INT_ASTORE(riv,OTHER_OPERAND(riv,riv))
    // 414: stm: SHORT_ASTORE(riv,OTHER_OPERAND(r,r))
    // 413: stm: SHORT_ASTORE(load16,OTHER_OPERAND(riv,riv))
    // 412: stm: SHORT_ASTORE(riv,OTHER_OPERAND(riv,riv))
    // 411: stm: SHORT_STORE(riv,OTHER_OPERAND(rlv,rlv))
    // 410: stm: SHORT_STORE(rlv,OTHER_OPERAND(rlv,rlv))
    // 409: stm: SHORT_STORE(load16,OTHER_OPERAND(riv,riv))
    // 408: stm: SHORT_STORE(riv,OTHER_OPERAND(riv,riv))
    else if (eruleno <= 476) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2(), ntsrule[2]);
    }
    // 478: stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(rlv,riv))
    // 477: stm: LONG_ASTORE(LONG_CONSTANT,OTHER_OPERAND(riv,riv))
    else if (eruleno <= 478) {
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2(), ntsrule[1]);
    }
    // 481: r: SYSCALL(INT_CONSTANT,any)
    // 480: r: CALL(INT_CONSTANT,any)
    // 479: r: CALL(BRANCH_TARGET,any)
    else if (eruleno <= 481) {
      mark(p.getChild2(), ntsrule[0]);
    }
    // 484: r: SYSCALL(INT_LOAD(riv,riv),any)
    // 483: r: CALL(LONG_LOAD(rlv,rlv),any)
    // 482: r: CALL(INT_LOAD(riv,riv),any)
    else if (eruleno <= 484) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild2(), ntsrule[2]);
    }
    // 500: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(double_load,r)))
    // 499: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(float_load,r)))
    // 498: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,double_load)))
    // 497: r: FCMP_FCMOV(r,OTHER_OPERAND(r,OTHER_OPERAND(r,float_load)))
    // 496: r: ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
    // 495: r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv)))
    // 494: r: ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv)))
    // 493: r: ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv)))
    // 492: r: ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv)))
    // 491: r: ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
    // 490: r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv)))
    // 489: r: ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv)))
    // 488: r: ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv)))
    // 487: r: ATTEMPT_INT(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
    // 486: r: ATTEMPT_INT(riv,OTHER_OPERAND(rlv,OTHER_OPERAND(riv,riv)))
    // 485: r: ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv)))
    else if (eruleno <= 500) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[3]);
    }
    // 502: r: ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv)))
    // 501: r: ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv)))
    else if (eruleno <= 502) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 504: r: ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv)))
    // 503: r: ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv)))
    else if (eruleno <= 504) {
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 524: stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 523: stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 522: stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 521: stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 520: stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 519: stm: INT_IFCMP(ATTEMPT_LONG(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 518: stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 517: stm: INT_IFCMP(ATTEMPT_LONG(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 516: stm: INT_IFCMP(ATTEMPT_LONG(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 515: stm: INT_IFCMP(ATTEMPT_LONG(rlv,OTHER_OPERAND(rlv,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 514: stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 513: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 512: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 511: stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 510: stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 509: stm: INT_IFCMP(ATTEMPT_INT(address1reg,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 508: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(address1reg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 507: stm: INT_IFCMP(ATTEMPT_INT(address1scaledreg,OTHER_OPERAND(r,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 506: stm: INT_IFCMP(ATTEMPT_INT(r,OTHER_OPERAND(address1scaledreg,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 505: stm: INT_IFCMP(ATTEMPT_INT(riv,OTHER_OPERAND(riv,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    else if (eruleno <= 524) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild1().getChild2().getChild2().getChild2(), ntsrule[3]);
    }
    // 528: stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 527: stm: INT_IFCMP(ATTEMPT_LONG(address,OTHER_OPERAND(LONG_CONSTANT,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 526: stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 525: stm: INT_IFCMP(ATTEMPT_INT(address,OTHER_OPERAND(INT_CONSTANT,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    else if (eruleno <= 528) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 532: stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 531: stm: INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    // 530: stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    // 529: stm: INT_IFCMP(ATTEMPT_INT(INT_CONSTANT,OTHER_OPERAND(address,OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    else if (eruleno <= 532) {
      mark(p.getChild1().getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 536: bittest: INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    // 535: bittest: INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    // 534: bittest: INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    // 533: bittest: INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    else if (eruleno <= 536) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
    }
    // 538: bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)),load32)
    // 537: bittest: INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
    else if (eruleno <= 538) {
      mark(p.getChild1().getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2(), ntsrule[1]);
    }
    // 540: bittest: INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
    // 539: bittest: INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r,INT_CONSTANT)))
    else if (eruleno <= 540) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
    }
    // 562: stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
    // 561: stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
    // 560: stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
    // 559: stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),LONG_CONSTANT),OTHER_OPERAND(riv,riv))
    // 558: stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 557: stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 556: stm: LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 555: stm: LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 554: stm: LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 553: stm: LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 552: stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 551: stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 550: stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 549: stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 548: stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 547: stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_CONSTANT),OTHER_OPERAND(riv,riv))
    // 546: stm: INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 545: stm: INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 544: stm: INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 543: stm: INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 542: stm: BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv,riv))
    // 541: stm: BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    else if (eruleno <= 562) {
      mark(p.getChild1().getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2(), ntsrule[3]);
    }
    // 571: r: LCMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
    // 570: r: CMP_CMOV(szp,OTHER_OPERAND(INT_CONSTANT,any))
    // 569: r: CMP_CMOV(cz,OTHER_OPERAND(INT_CONSTANT,any))
    // 568: r: CMP_CMOV(bittest,OTHER_OPERAND(INT_CONSTANT,any))
    // 567: r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
    // 566: r: CMP_CMOV(boolcmp,OTHER_OPERAND(INT_CONSTANT,any))
    // 565: r: CMP_CMOV(sload16,OTHER_OPERAND(INT_CONSTANT,any))
    // 564: r: CMP_CMOV(load8,OTHER_OPERAND(INT_CONSTANT,any))
    // 563: r: CMP_CMOV(r,OTHER_OPERAND(INT_CONSTANT,any))
    else if (eruleno <= 571) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2(), ntsrule[1]);
    }
    // 579: stm: INT_ASTORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
    // 578: stm: INT_STORE(LONG_2INT(r),OTHER_OPERAND(riv,riv))
    // 577: stm: SHORT_ASTORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
    // 576: stm: SHORT_STORE(INT_2USHORT(r),OTHER_OPERAND(riv,riv))
    // 575: stm: SHORT_ASTORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
    // 574: stm: SHORT_STORE(INT_2SHORT(r),OTHER_OPERAND(riv,riv))
    // 573: stm: BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
    // 572: stm: BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 579) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2(), ntsrule[2]);
    }
    // 599: stm: LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 598: stm: LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 597: stm: LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 596: stm: LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 595: stm: LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 594: stm: LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 593: stm: LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 592: stm: LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 591: stm: LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 590: stm: LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv,rlv))
    // 589: stm: INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 588: stm: INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 587: stm: INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 586: stm: INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 585: stm: INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 584: stm: INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 583: stm: INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 582: stm: INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 581: stm: INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    // 580: stm: INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 599) {
      mark(p.getChild1().getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild1().getChild2(), ntsrule[2]);
      mark(p.getChild2().getChild1(), ntsrule[3]);
      mark(p.getChild2().getChild2(), ntsrule[4]);
    }
    // 619: stm: LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 618: stm: LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 617: stm: LONG_ASTORE(LONG_SUB(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 616: stm: LONG_STORE(LONG_SUB(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 615: stm: LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 614: stm: LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 613: stm: LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 612: stm: LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 611: stm: LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 610: stm: LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv,rlv))
    // 609: stm: INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 608: stm: INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 607: stm: INT_ASTORE(INT_SUB(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 606: stm: INT_STORE(INT_SUB(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 605: stm: INT_ASTORE(INT_OR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 604: stm: INT_STORE(INT_OR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 603: stm: INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 602: stm: INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 601: stm: INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    // 600: stm: INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 619) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild2(), ntsrule[2]);
      mark(p.getChild2().getChild1(), ntsrule[3]);
      mark(p.getChild2().getChild2(), ntsrule[4]);
    }
    // 623: r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    // 622: r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    // 621: r: INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    // 620: r: INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    else if (eruleno <= 623) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
    }
    // 625: r: INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    // 624: r: INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    else if (eruleno <= 625) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2().getChild1().getChild1(), ntsrule[3]);
    }
    // 627: r: INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
    // 626: r: INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
    else if (eruleno <= 627) {
      mark(p.getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild2().getChild1().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[3]);
    }
    // 635: szpr: LONG_USHR(rlv,LONG_AND(r,LONG_CONSTANT))
    // 634: stm: LONG_STORE(rlv,OTHER_OPERAND(address,LONG_CONSTANT))
    // 633: szpr: LONG_SHR(rlv,INT_AND(r,LONG_CONSTANT))
    // 632: szpr: LONG_SHL(rlv,INT_AND(r,INT_CONSTANT))
    // 631: szpr: INT_USHR(riv,INT_AND(r,INT_CONSTANT))
    // 630: stm: INT_STORE(riv,OTHER_OPERAND(address,LONG_CONSTANT))
    // 629: szpr: INT_SHR(riv,INT_AND(r,INT_CONSTANT))
    // 628: szpr: INT_SHL(riv,INT_AND(r,INT_CONSTANT))
    else if (eruleno <= 635) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild1(), ntsrule[1]);
    }
    // 647: stm: LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 646: stm: LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 645: stm: LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 644: stm: LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 643: stm: LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 642: stm: LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 641: stm: INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 640: stm: INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 639: stm: INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 638: stm: INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 637: stm: INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    // 636: stm: INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv,riv))
    else if (eruleno <= 647) {
      mark(p.getChild1().getChild1().getChild1(), ntsrule[0]);
      mark(p.getChild1().getChild1().getChild2(), ntsrule[1]);
      mark(p.getChild1().getChild2().getChild1(), ntsrule[2]);
      mark(p.getChild2().getChild1(), ntsrule[3]);
      mark(p.getChild2().getChild2(), ntsrule[4]);
    }
    // 651: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 650: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 649: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
    // 648: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,FLOAT_NEG(r))))
    else if (eruleno <= 651) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2().getChild1(), ntsrule[2]);
    }
    // 655: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 654: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 653: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
    // 652: r: FCMP_FCMOV(r,OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(FLOAT_NEG(r),r)))
    else if (eruleno <= 655) {
      mark(p.getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 659: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 658: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(DOUBLE_NEG(r),r)))
    // 657: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
    // 656: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(FLOAT_NEG(r),r)))
    else if (eruleno <= 659) {
      mark(p.getChild2().getChild1(), ntsrule[0]);
      mark(p.getChild2().getChild2().getChild1().getChild1(), ntsrule[1]);
      mark(p.getChild2().getChild2().getChild2(), ntsrule[2]);
    }
    // 663: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 662: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,DOUBLE_NEG(r))))
    // 661: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
    // 660: r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT),OTHER_OPERAND(r,OTHER_OPERAND(r,FLOAT_NEG(r))))
    else {
      if (VM.VerifyAssertions) VM._assert(eruleno <= 663);
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
    NOFLAGS, // 85 - address1scaledreg:	address1reg
    NOFLAGS, // 86 - address:	address1scaledreg
    EMIT_INSTRUCTION, // 87 - address1scaledreg:	INT_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 88 - address1reg:	INT_ADD(r, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 89 - address1reg:	INT_MOVE(r)
    EMIT_INSTRUCTION, // 90 - address:	INT_ADD(r, r)
    EMIT_INSTRUCTION, // 91 - address1reg:	INT_ADD(address1reg, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 92 - address1scaledreg:	INT_ADD(address1scaledreg, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 93 - address:	INT_ADD(r, address1scaledreg)
    EMIT_INSTRUCTION, // 94 - address:	INT_ADD(address1scaledreg, r)
    EMIT_INSTRUCTION, // 95 - address:	INT_ADD(address1scaledreg, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 96 - address:	INT_ADD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 97 - address:	INT_ADD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 98 - address1scaledreg:	LONG_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 99 - address1reg:	LONG_ADD(r, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 100 - address1reg:	LONG_MOVE(r)
    EMIT_INSTRUCTION, // 101 - address:	LONG_ADD(r, r)
    EMIT_INSTRUCTION, // 102 - address1reg:	LONG_ADD(address1reg, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 103 - address1scaledreg:	LONG_ADD(address1scaledreg, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 104 - address:	LONG_ADD(r, address1scaledreg)
    EMIT_INSTRUCTION, // 105 - address:	LONG_ADD(address1scaledreg, r)
    EMIT_INSTRUCTION, // 106 - address:	LONG_ADD(address1scaledreg, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 107 - address:	LONG_ADD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 108 - address:	LONG_ADD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 109 - r:	ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 110 - r:	ATTEMPT_INT(riv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 111 - r:	ATTEMPT_INT(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 112 - r:	ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 113 - r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 114 - r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 115 - r:	ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 116 - r:	ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 117 - r:	ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv, riv)))
    EMIT_INSTRUCTION, // 118 - stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 119 - stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 120 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 121 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 122 - stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 123 - stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 124 - stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 125 - stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))), INT_CONSTANT)
    EMIT_INSTRUCTION, // 126 - stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 127 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 128 - stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 129 - stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 130 - stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 131 - stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 132 - r:	ATTEMPT_LONG(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 133 - r:	ATTEMPT_LONG(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 134 - r:	ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 135 - r:	ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 136 - r:	ATTEMPT_LONG(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 137 - r:	ATTEMPT_LONG(address, OTHER_OPERAND(LONG_CONSTANT, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 138 - r:	ATTEMPT_LONG(LONG_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(rlv, rlv)))
    EMIT_INSTRUCTION, // 139 - stm:	INT_IFCMP(ATTEMPT_LONG(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 140 - stm:	INT_IFCMP(ATTEMPT_LONG(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 141 - stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 142 - stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 143 - stm:	INT_IFCMP(ATTEMPT_LONG(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 144 - stm:	INT_IFCMP(ATTEMPT_LONG(address, OTHER_OPERAND(LONG_CONSTANT, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 145 - stm:	INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 146 - stm:	INT_IFCMP(ATTEMPT_LONG(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(rlv,rlv))), INT_CONSTANT)
    EMIT_INSTRUCTION, // 147 - stm:	INT_IFCMP(ATTEMPT_LONG(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 148 - stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 149 - stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 150 - stm:	INT_IFCMP(ATTEMPT_LONG(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 151 - stm:	INT_IFCMP(ATTEMPT_LONG(address, OTHER_OPERAND(LONG_CONSTANT, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 152 - stm:	INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
    EMIT_INSTRUCTION, // 153 - bittest:	INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 154 - bittest:	INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 155 - bittest:	INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
    EMIT_INSTRUCTION, // 156 - bittest:	INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 157 - bittest:	INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
    EMIT_INSTRUCTION, // 158 - bittest:	INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
    EMIT_INSTRUCTION, // 159 - bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
    EMIT_INSTRUCTION, // 160 - bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)),load32)
    EMIT_INSTRUCTION, // 161 - bittest:	INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 162 - bittest:	INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 163 - r:	BOOLEAN_CMP_INT(r,riv)
    EMIT_INSTRUCTION, // 164 - boolcmp: BOOLEAN_CMP_INT(r,riv)
    EMIT_INSTRUCTION, // 165 - r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 166 - boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 167 - r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 168 - r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    EMIT_INSTRUCTION, // 169 - r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
    EMIT_INSTRUCTION, // 170 - r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
    EMIT_INSTRUCTION, // 171 - r:	BOOLEAN_CMP_INT(cz, INT_CONSTANT)
    EMIT_INSTRUCTION, // 172 - boolcmp: BOOLEAN_CMP_INT(cz, INT_CONSTANT)
    EMIT_INSTRUCTION, // 173 - r:	BOOLEAN_CMP_INT(szp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 174 - boolcmp: BOOLEAN_CMP_INT(szp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 175 - r:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
    EMIT_INSTRUCTION, // 176 - boolcmp:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
    EMIT_INSTRUCTION, // 177 - r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    NOFLAGS, // 178 - boolcmp:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 179 - r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 180 - boolcmp:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 181 - r:	BOOLEAN_CMP_INT(load32,riv)
    EMIT_INSTRUCTION, // 182 - boolcmp: BOOLEAN_CMP_INT(load32,riv)
    EMIT_INSTRUCTION, // 183 - r:	BOOLEAN_CMP_INT(r,load32)
    EMIT_INSTRUCTION, // 184 - boolcmp: BOOLEAN_CMP_INT(riv,load32)
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 185 - stm:	BYTE_STORE(boolcmp, OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 186 - stm:	BYTE_ASTORE(boolcmp, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 187 - r:	BOOLEAN_CMP_LONG(r,rlv)
    EMIT_INSTRUCTION, // 188 - boolcmp: BOOLEAN_CMP_LONG(r,rlv)
    EMIT_INSTRUCTION, // 189 - r:	BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    EMIT_INSTRUCTION, // 190 - boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    EMIT_INSTRUCTION, // 191 - r:	BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    EMIT_INSTRUCTION, // 192 - r:	BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
    EMIT_INSTRUCTION, // 193 - r:	BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
    EMIT_INSTRUCTION, // 194 - r:	BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
    EMIT_INSTRUCTION, // 195 - r:	BOOLEAN_CMP_LONG(cz, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 196 - r:	BOOLEAN_CMP_LONG(load64,rlv)
    EMIT_INSTRUCTION, // 197 - boolcmp: BOOLEAN_CMP_LONG(load64,rlv)
    EMIT_INSTRUCTION, // 198 - r:	BOOLEAN_CMP_LONG(r,load64)
    EMIT_INSTRUCTION, // 199 - boolcmp: BOOLEAN_CMP_LONG(rlv,load64)
    EMIT_INSTRUCTION, // 200 - r:	BOOLEAN_NOT(r)
    EMIT_INSTRUCTION, // 201 - stm:	BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 202 - stm:	BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 203 - stm:    BYTE_STORE(riv, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 204 - stm:    BYTE_STORE(load8, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 205 - stm:    BYTE_ASTORE(riv, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 206 - stm:    BYTE_ASTORE(load8, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 207 - r: CMP_CMOV(r, OTHER_OPERAND(riv, any))
    EMIT_INSTRUCTION, // 208 - r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 209 - r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 210 - r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 211 - r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 212 - r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
    EMIT_INSTRUCTION, // 213 - r: CMP_CMOV(load8, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 214 - r: CMP_CMOV(uload8, OTHER_OPERAND(riv, any))
    EMIT_INSTRUCTION, // 215 - r: CMP_CMOV(riv, OTHER_OPERAND(uload8, any))
    EMIT_INSTRUCTION, // 216 - r: CMP_CMOV(sload16, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 217 - r: CMP_CMOV(load32, OTHER_OPERAND(riv, any))
    EMIT_INSTRUCTION, // 218 - r: CMP_CMOV(riv, OTHER_OPERAND(load32, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 219 - r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 220 - r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 221 - r: CMP_CMOV(bittest, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 222 - r: CMP_CMOV(cz, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION | RIGHT_CHILD_FIRST, // 223 - r: CMP_CMOV(szp, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 224 - r:	INT_2BYTE(r)
    EMIT_INSTRUCTION, // 225 - r:	INT_2BYTE(load8_16_32)
    EMIT_INSTRUCTION, // 226 - stm:	BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 227 - stm:	BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 228 - r:	INT_2LONG(r)
    EMIT_INSTRUCTION, // 229 - r:	INT_2LONG(load32)
    EMIT_INSTRUCTION, // 230 - r:      LONG_AND(INT_2LONG(r), LONG_CONSTANT)
    EMIT_INSTRUCTION, // 231 - r:      LONG_AND(INT_2LONG(load32), LONG_CONSTANT)
    EMIT_INSTRUCTION, // 232 - r:	INT_2ADDRZerExt(r)
    EMIT_INSTRUCTION, // 233 - r:	INT_2SHORT(r)
    EMIT_INSTRUCTION, // 234 - r:	INT_2SHORT(load16_32)
    EMIT_INSTRUCTION, // 235 - sload16:	INT_2SHORT(load16_32)
    EMIT_INSTRUCTION, // 236 - stm:	SHORT_STORE(INT_2SHORT(r), OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION, // 237 - stm:	SHORT_ASTORE(INT_2SHORT(r), OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 238 - szpr:	INT_2USHORT(r)
    EMIT_INSTRUCTION, // 239 - uload16:	INT_2USHORT(load16_32)
    EMIT_INSTRUCTION, // 240 - r:	INT_2USHORT(load16_32)
    EMIT_INSTRUCTION, // 241 - stm:	SHORT_STORE(INT_2USHORT(r), OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION, // 242 - stm:	SHORT_ASTORE(INT_2USHORT(r), OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 243 - czr:	INT_ADD(r, riv)
    EMIT_INSTRUCTION, // 244 - r:	INT_ADD(r, riv)
    EMIT_INSTRUCTION, // 245 - czr:	INT_ADD(r, load32)
    EMIT_INSTRUCTION, // 246 - czr:	INT_ADD(load32, riv)
    EMIT_INSTRUCTION, // 247 - stm:	INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 248 - stm:	INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 249 - stm:	INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 250 - stm:	INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 251 - szpr:	INT_AND(r, riv)
    EMIT_INSTRUCTION, // 252 - szp:	INT_AND(r, riv)
    EMIT_INSTRUCTION, // 253 - szpr:	INT_AND(r, load32)
    EMIT_INSTRUCTION, // 254 - szpr:	INT_AND(load32, riv)
    EMIT_INSTRUCTION, // 255 - szp:	INT_AND(load8_16_32, riv)
    EMIT_INSTRUCTION, // 256 - szp:	INT_AND(r, load8_16_32)
    EMIT_INSTRUCTION, // 257 - stm:	INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 258 - stm:	INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 259 - stm:	INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 260 - stm:	INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 261 - r:	INT_DIV(riv, riv)
    EMIT_INSTRUCTION, // 262 - r:	INT_DIV(riv, load32)
    EMIT_INSTRUCTION, // 263 - r:     UNSIGNED_DIV_64_32(rlv, riv)
    EMIT_INSTRUCTION, // 264 - r:     UNSIGNED_DIV_64_32(rlv, load32)
    EMIT_INSTRUCTION, // 265 - stm:	INT_IFCMP(r,riv)
    EMIT_INSTRUCTION, // 266 - stm:	INT_IFCMP(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 267 - stm:	INT_IFCMP(load8, INT_CONSTANT)
    EMIT_INSTRUCTION, // 268 - stm:	INT_IFCMP(uload8, r)
    EMIT_INSTRUCTION, // 269 - stm:	INT_IFCMP(r, uload8)
    EMIT_INSTRUCTION, // 270 - stm:	INT_IFCMP(sload16, INT_CONSTANT)
    EMIT_INSTRUCTION, // 271 - stm:	INT_IFCMP(load32, riv)
    EMIT_INSTRUCTION, // 272 - stm:	INT_IFCMP(r, load32)
    EMIT_INSTRUCTION, // 273 - stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 274 - stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 275 - stm:	INT_IFCMP(cz, INT_CONSTANT)
    EMIT_INSTRUCTION, // 276 - stm:	INT_IFCMP(szp, INT_CONSTANT)
    EMIT_INSTRUCTION, // 277 - stm:	INT_IFCMP(bittest, INT_CONSTANT)
    EMIT_INSTRUCTION, // 278 - stm:	INT_IFCMP2(r,riv)
    EMIT_INSTRUCTION, // 279 - stm:	INT_IFCMP2(load32,riv)
    EMIT_INSTRUCTION, // 280 - stm:	INT_IFCMP2(riv,load32)
    EMIT_INSTRUCTION, // 281 - r:	INT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 282 - r:	INT_LOAD(rlv, address1scaledreg)
    EMIT_INSTRUCTION, // 283 - r:	INT_LOAD(address1scaledreg, rlv)
    EMIT_INSTRUCTION, // 284 - r:	INT_LOAD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 285 - r:	INT_LOAD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 286 - r:	INT_LOAD(address, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 287 - r:      INT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 288 - r:	INT_MOVE(riv)
    EMIT_INSTRUCTION, // 289 - czr:	INT_MOVE(czr)
    NOFLAGS, // 290 - cz:	INT_MOVE(cz)
    EMIT_INSTRUCTION, // 291 - szpr:	INT_MOVE(szpr)
    NOFLAGS, // 292 - szp:	INT_MOVE(szp)
    NOFLAGS, // 293 - sload8:	INT_MOVE(sload8)
    NOFLAGS, // 294 - uload8:	INT_MOVE(uload8)
    NOFLAGS, // 295 - load8:	INT_MOVE(load8)
    NOFLAGS, // 296 - sload16: INT_MOVE(sload16)
    NOFLAGS, // 297 - uload16: INT_MOVE(uload16)
    NOFLAGS, // 298 - load16:	INT_MOVE(load16)
    NOFLAGS, // 299 - load32:	INT_MOVE(load32)
    EMIT_INSTRUCTION, // 300 - r:	INT_MUL(r, riv)
    EMIT_INSTRUCTION, // 301 - r:	INT_MUL(r, load32)
    EMIT_INSTRUCTION, // 302 - r:	INT_MUL(load32, riv)
    EMIT_INSTRUCTION, // 303 - szpr:	INT_NEG(r)
    EMIT_INSTRUCTION, // 304 - stm:	INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 305 - stm:	INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 306 - r:	INT_NOT(r)
    EMIT_INSTRUCTION, // 307 - stm:	INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 308 - stm:	INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 309 - szpr:	INT_OR(r, riv)
    EMIT_INSTRUCTION, // 310 - szpr:	INT_OR(r, load32)
    EMIT_INSTRUCTION, // 311 - szpr:	INT_OR(load32, riv)
    EMIT_INSTRUCTION, // 312 - stm:	INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 313 - stm:	INT_STORE(INT_OR(r, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 314 - stm:	INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 315 - stm:	INT_ASTORE(INT_OR(r, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 316 - r:	INT_REM(riv, riv)
    EMIT_INSTRUCTION, // 317 - r:	INT_REM(riv, load32)
    EMIT_INSTRUCTION, // 318 - r:     UNSIGNED_REM_64_32(rlv, riv)
    EMIT_INSTRUCTION, // 319 - r:     UNSIGNED_REM_64_32(rlv, load32)
    EMIT_INSTRUCTION, // 320 - r:	INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 321 - r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 322 - r:      INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 323 - r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
    EMIT_INSTRUCTION, // 324 - r:      INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    EMIT_INSTRUCTION, // 325 - r:      INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
    EMIT_INSTRUCTION, // 326 - r:      INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
    EMIT_INSTRUCTION, // 327 - r:      INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
    EMIT_INSTRUCTION, // 328 - szpr:	INT_SHL(riv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 329 - szpr:	INT_SHL(riv, riv)
    EMIT_INSTRUCTION, // 330 - szpr:	INT_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 331 - r:	INT_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 332 - szpr:	INT_SHL(INT_SHR(r, INT_CONSTANT), INT_CONSTANT)
    EMIT_INSTRUCTION, // 333 - stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 334 - stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 335 - stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 336 - stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 337 - szpr:	INT_SHR(riv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 338 - szpr:	INT_SHR(riv, riv)
    EMIT_INSTRUCTION, // 339 - szpr:	INT_SHR(riv, INT_CONSTANT)
    EMIT_INSTRUCTION, // 340 - stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 341 - stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 342 - stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 343 - stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 344 - stm:	INT_STORE(riv, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 345 - stm:	INT_STORE(riv, OTHER_OPERAND(rlv, address1scaledreg))
    EMIT_INSTRUCTION, // 346 - stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, rlv))
    EMIT_INSTRUCTION, // 347 - stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, address1reg))
    EMIT_INSTRUCTION, // 348 - stm:	INT_STORE(riv, OTHER_OPERAND(address1reg, address1scaledreg))
    EMIT_INSTRUCTION, // 349 - stm:	INT_STORE(riv, OTHER_OPERAND(address, LONG_CONSTANT))
    EMIT_INSTRUCTION, // 350 - czr:	INT_SUB(riv, r)
    EMIT_INSTRUCTION, // 351 - r:	INT_SUB(riv, r)
    EMIT_INSTRUCTION, // 352 - r:	INT_SUB(load32, r)
    EMIT_INSTRUCTION, // 353 - czr:	INT_SUB(riv, load32)
    EMIT_INSTRUCTION, // 354 - czr:	INT_SUB(load32, riv)
    EMIT_INSTRUCTION, // 355 - stm:	INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 356 - stm:	INT_STORE(INT_SUB(riv, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 357 - stm:	INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 358 - stm:	INT_ASTORE(INT_SUB(riv, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 359 - szpr:	INT_USHR(riv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 360 - szpr:	INT_USHR(riv, riv)
    EMIT_INSTRUCTION, // 361 - szpr:	INT_USHR(riv, INT_CONSTANT)
    EMIT_INSTRUCTION, // 362 - stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 363 - stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 364 - stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 365 - stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 366 - szpr:	INT_XOR(r, riv)
    EMIT_INSTRUCTION, // 367 - szpr:	INT_XOR(r, load32)
    EMIT_INSTRUCTION, // 368 - szpr:	INT_XOR(load32, riv)
    EMIT_INSTRUCTION, // 369 - stm:	INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 370 - stm:	INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 371 - stm:	INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 372 - stm:	INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 373 - r: LCMP_CMOV(r, OTHER_OPERAND(rlv, any))
    EMIT_INSTRUCTION, // 374 - r: LCMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, any))
    EMIT_INSTRUCTION, // 375 - r: LCMP_CMOV(load64, OTHER_OPERAND(rlv, any))
    EMIT_INSTRUCTION, // 376 - r: LCMP_CMOV(rlv, OTHER_OPERAND(load64, any))
    EMIT_INSTRUCTION, // 377 - r:	LONG_ADD(address1scaledreg, r)
    EMIT_INSTRUCTION, // 378 - r:	LONG_ADD(r, address1scaledreg)
    EMIT_INSTRUCTION, // 379 - r:	LONG_ADD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 380 - r:	LONG_ADD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 381 - r:	LONG_ADD(address, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 382 - r:	LONG_MOVE(address)
    EMIT_INSTRUCTION, // 383 - r:      BYTE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 384 - sload8:	BYTE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 385 - r:      BYTE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 386 - r:      BYTE_ALOAD(rlv, r)
    EMIT_INSTRUCTION, // 387 - sload8:	BYTE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 388 - r:      UBYTE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 389 - uload8:	UBYTE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 390 - r:	UBYTE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 391 - r:      UBYTE_ALOAD(rlv, r)
    EMIT_INSTRUCTION, // 392 - uload8:	UBYTE_ALOAD(rlv, riv)
    NOFLAGS, // 393 - load8:	sload8
    NOFLAGS, // 394 - load8:	uload8
    EMIT_INSTRUCTION, // 395 - r:      SHORT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 396 - sload16: SHORT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 397 - r:      SHORT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 398 - r:      SHORT_ALOAD(rlv, r)
    EMIT_INSTRUCTION, // 399 - sload16: SHORT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 400 - r:      USHORT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 401 - uload16: USHORT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 402 - r:      USHORT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 403 - r:      USHORT_ALOAD(rlv, r)
    EMIT_INSTRUCTION, // 404 - uload16: USHORT_ALOAD(rlv, riv)
    NOFLAGS, // 405 - load16:	sload16
    NOFLAGS, // 406 - load16:	uload16
    EMIT_INSTRUCTION, // 407 - load32:	INT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 408 - load32:	INT_ALOAD(rlv, riv)
    NOFLAGS, // 409 - load16_32:      load16
    NOFLAGS, // 410 - load16_32:      load32
    NOFLAGS, // 411 - load8_16_32:	load16_32
    NOFLAGS, // 412 - load8_16_32:	load8
    EMIT_INSTRUCTION, // 413 - load64:	LONG_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 414 - load64:	LONG_ALOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 415 - load64:	LONG_ALOAD(rlv, r)
    NOFLAGS, // 416 - load8_16_32_64:	load64
    NOFLAGS, // 417 - load8_16_32_64:	load8_16_32
    EMIT_INSTRUCTION, // 418 - r:	LONG_2INT(r)
    EMIT_INSTRUCTION, // 419 - stm:	INT_STORE(LONG_2INT(r), OTHER_OPERAND(riv,riv))
    EMIT_INSTRUCTION, // 420 - stm:	INT_ASTORE(LONG_2INT(r), OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 421 - r:	LONG_2INT(load64)
    EMIT_INSTRUCTION, // 422 - load32:      LONG_2INT(load64)
    EMIT_INSTRUCTION, // 423 - r:	LONG_2INT(LONG_USHR(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 424 - r:      LONG_2INT(LONG_SHR(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 425 - r:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 426 - r:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 427 - load32:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 428 - load32:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
    EMIT_INSTRUCTION, // 429 - czr:	LONG_ADD(r, rlv)
    EMIT_INSTRUCTION, // 430 - czr:	LONG_ADD(r, riv)
    EMIT_INSTRUCTION, // 431 - czr:    LONG_ADD(r,r)
    EMIT_INSTRUCTION, // 432 - r:	LONG_ADD(r, rlv)
    EMIT_INSTRUCTION, // 433 - czr:	LONG_ADD(rlv, load64)
    EMIT_INSTRUCTION, // 434 - czr:	LONG_ADD(load64, rlv)
    EMIT_INSTRUCTION, // 435 - stm:	LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 436 - stm:	LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 437 - stm:	LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 438 - stm:	LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 439 - szpr:	LONG_AND(r, rlv)
    EMIT_INSTRUCTION, // 440 - szpr:    LONG_AND(r,r)
    EMIT_INSTRUCTION, // 441 - szp:	LONG_AND(r, rlv)
    EMIT_INSTRUCTION, // 442 - szpr:	LONG_AND(rlv, load64)
    EMIT_INSTRUCTION, // 443 - szpr:	LONG_AND(load64, rlv)
    EMIT_INSTRUCTION, // 444 - szp:	LONG_AND(load8_16_32_64, rlv)
    EMIT_INSTRUCTION, // 445 - szp:	LONG_AND(r, load8_16_32_64)
    EMIT_INSTRUCTION, // 446 - stm:	LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 447 - stm:	LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 448 - stm:	LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 449 - stm:	LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 450 - r:  LONG_DIV(rlv, rlv)
    EMIT_INSTRUCTION, // 451 - r:  LONG_DIV(rlv, riv)
    EMIT_INSTRUCTION, // 452 - r:  LONG_DIV(riv, rlv)
    EMIT_INSTRUCTION, // 453 - r:  LONG_DIV(rlv, load64)
    EMIT_INSTRUCTION, // 454 - r:  LONG_DIV(load64,rlv)
    EMIT_INSTRUCTION, // 455 - stm:	LONG_IFCMP(rlv,rlv)
    EMIT_INSTRUCTION, // 456 - stm:	LONG_IFCMP(r, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 457 - r:	LONG_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 458 - r:	LONG_LOAD(rlv, address1scaledreg)
    EMIT_INSTRUCTION, // 459 - r:	LONG_LOAD(address1scaledreg, rlv)
    EMIT_INSTRUCTION, // 460 - r:	LONG_LOAD(address1scaledreg, address1reg)
    EMIT_INSTRUCTION, // 461 - r:	LONG_LOAD(address1reg, address1scaledreg)
    EMIT_INSTRUCTION, // 462 - r:	LONG_LOAD(address, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 463 - r:      LONG_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 464 - r:      LONG_ALOAD(rlv, r)
    EMIT_INSTRUCTION, // 465 - r:	LONG_MOVE(rlv)
    EMIT_INSTRUCTION, // 466 - r:  LONG_MOVE(riv)
    NOFLAGS, // 467 - load64:	LONG_MOVE(load64)
    EMIT_INSTRUCTION, // 468 - r:	LONG_MUL(r, rlv)
    EMIT_INSTRUCTION, // 469 - r:	INT_MUL(r, load64)
    EMIT_INSTRUCTION, // 470 - r:	INT_MUL(load64, rlv)
    EMIT_INSTRUCTION, // 471 - szpr:	LONG_NEG(r)
    EMIT_INSTRUCTION, // 472 - stm:	LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 473 - stm:	LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 474 - r:	LONG_NOT(r)
    EMIT_INSTRUCTION, // 475 - stm:	LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 476 - stm:	LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 477 - szpr:	LONG_OR(r, rlv)
    EMIT_INSTRUCTION, // 478 - szpr:	LONG_OR(r, load64)
    EMIT_INSTRUCTION, // 479 - szpr:	LONG_OR(load64, rlv)
    EMIT_INSTRUCTION, // 480 - stm:	LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 481 - stm:	LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 482 - stm:	LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 483 - stm:	LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 484 - r:  LONG_REM(rlv, rlv)
    EMIT_INSTRUCTION, // 485 - r:  LONG_REM(rlv, riv)
    EMIT_INSTRUCTION, // 486 - r:  LONG_REM(riv, rlv)
    EMIT_INSTRUCTION, // 487 - r:  LONG_REM(rlv, load64)
    EMIT_INSTRUCTION, // 488 - r:  LONG_REM(load64,rlv)
    EMIT_INSTRUCTION, // 489 - szpr:	LONG_SHL(rlv, INT_AND(r, INT_CONSTANT))
    EMIT_INSTRUCTION, // 490 - szpr:	LONG_SHL(rlv, riv)
    EMIT_INSTRUCTION, // 491 - szpr:	LONG_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 492 - r:	LONG_SHL(r, INT_CONSTANT)
    EMIT_INSTRUCTION, // 493 - szpr:	LONG_SHL(LONG_SHR(r, INT_CONSTANT), INT_CONSTANT)
    EMIT_INSTRUCTION, // 494 - stm:	LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 495 - stm:	LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 496 - stm:	LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 497 - stm:	LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 498 - szpr:	LONG_SHR(rlv, INT_AND(r, LONG_CONSTANT))
    EMIT_INSTRUCTION, // 499 - szpr:	LONG_SHR(rlv, riv)
    EMIT_INSTRUCTION, // 500 - szpr:	LONG_SHR(rlv, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 501 - stm:	LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 502 - stm:	LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 503 - stm:	LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r, LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 504 - stm:	LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 505 - stm:	LONG_STORE(rlv, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 506 - stm:	LONG_STORE(rlv, OTHER_OPERAND(rlv, address1scaledreg))
    EMIT_INSTRUCTION, // 507 - stm:	LONG_STORE(rlv, OTHER_OPERAND(address1scaledreg, rlv))
    EMIT_INSTRUCTION, // 508 - stm:	LONG_STORE(rlv, OTHER_OPERAND(address1scaledreg, address1reg))
    EMIT_INSTRUCTION, // 509 - stm:	LONG_STORE(rlv, OTHER_OPERAND(address1reg, address1scaledreg))
    EMIT_INSTRUCTION, // 510 - stm:	LONG_STORE(rlv, OTHER_OPERAND(address, LONG_CONSTANT))
    EMIT_INSTRUCTION, // 511 - czr:	LONG_SUB(rlv, r)
    EMIT_INSTRUCTION, // 512 - r:	LONG_SUB(rlv, r)
    EMIT_INSTRUCTION, // 513 - r:	LONG_SUB(load64, r)
    EMIT_INSTRUCTION, // 514 - czr:	LONG_SUB(rlv, load64)
    EMIT_INSTRUCTION, // 515 - czr:	LONG_SUB(load64, rlv)
    EMIT_INSTRUCTION, // 516 - stm:	LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 517 - stm:	LONG_STORE(LONG_SUB(rlv, LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 518 - stm:	LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 519 - stm:	LONG_ASTORE(LONG_SUB(rlv, LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 520 - szpr:	LONG_USHR(rlv, LONG_AND(r, LONG_CONSTANT))
    EMIT_INSTRUCTION, // 521 - szpr:	LONG_USHR(rlv, riv)
    EMIT_INSTRUCTION, // 522 - szpr:	LONG_USHR(rlv, LONG_CONSTANT)
    EMIT_INSTRUCTION, // 523 - stm:	LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 524 - stm:	LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 525 - stm:	LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r, LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 526 - stm:	LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 527 - szpr:	LONG_XOR(r, rlv)
    EMIT_INSTRUCTION, // 528 - szpr:	LONG_XOR(r, load64)
    EMIT_INSTRUCTION, // 529 - szpr:	LONG_XOR(load64, rlv)
    EMIT_INSTRUCTION, // 530 - stm:	LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 531 - stm:	LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 532 - stm:	LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 533 - stm:	LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 534 - r: FLOAT_ADD(r, r)
    EMIT_INSTRUCTION, // 535 - r: FLOAT_ADD(r, float_load)
    EMIT_INSTRUCTION, // 536 - r: FLOAT_ADD(float_load,r)
    EMIT_INSTRUCTION, // 537 - r: DOUBLE_ADD(r, r)
    EMIT_INSTRUCTION, // 538 - r: DOUBLE_ADD(r, double_load)
    EMIT_INSTRUCTION, // 539 - r: DOUBLE_ADD(double_load,r)
    EMIT_INSTRUCTION, // 540 - r: FLOAT_SUB(r, r)
    EMIT_INSTRUCTION, // 541 - r: FLOAT_SUB(r, float_load)
    EMIT_INSTRUCTION, // 542 - r: DOUBLE_SUB(r, r)
    EMIT_INSTRUCTION, // 543 - r: DOUBLE_SUB(r, double_load)
    EMIT_INSTRUCTION, // 544 - r: FLOAT_MUL(r, r)
    EMIT_INSTRUCTION, // 545 - r: FLOAT_MUL(r, float_load)
    EMIT_INSTRUCTION, // 546 - r: FLOAT_MUL(float_load, r)
    EMIT_INSTRUCTION, // 547 - r: DOUBLE_MUL(r, r)
    EMIT_INSTRUCTION, // 548 - r: DOUBLE_MUL(r, double_load)
    EMIT_INSTRUCTION, // 549 - r: DOUBLE_MUL(double_load, r)
    EMIT_INSTRUCTION, // 550 - r: FLOAT_DIV(r, r)
    EMIT_INSTRUCTION, // 551 - r: FLOAT_DIV(r, float_load)
    EMIT_INSTRUCTION, // 552 - r: DOUBLE_DIV(r, r)
    EMIT_INSTRUCTION, // 553 - r: DOUBLE_DIV(r, double_load)
    EMIT_INSTRUCTION, // 554 - r: FLOAT_NEG(r)
    EMIT_INSTRUCTION, // 555 - r: DOUBLE_NEG(r)
    EMIT_INSTRUCTION, // 556 - r: FLOAT_SQRT(r)
    EMIT_INSTRUCTION, // 557 - r: DOUBLE_SQRT(r)
    EMIT_INSTRUCTION, // 558 - r: FLOAT_REM(r, r)
    EMIT_INSTRUCTION, // 559 - r: DOUBLE_REM(r, r)
    EMIT_INSTRUCTION, // 560 - r: LONG_2FLOAT(r)
    EMIT_INSTRUCTION, // 561 - r: LONG_2DOUBLE(r)
    EMIT_INSTRUCTION, // 562 - r: FLOAT_MOVE(r)
    EMIT_INSTRUCTION, // 563 - r: DOUBLE_MOVE(r)
    EMIT_INSTRUCTION, // 564 - r: DOUBLE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 565 - r: DOUBLE_LOAD(riv, rlv)
    EMIT_INSTRUCTION, // 566 - r: DOUBLE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 567 - double_load: DOUBLE_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 568 - r: DOUBLE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 569 - r: DOUBLE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 570 - double_load: DOUBLE_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 571 - r: DOUBLE_ALOAD(riv, r)
    EMIT_INSTRUCTION, // 572 - r: DOUBLE_ALOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 573 - double_load: DOUBLE_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 574 - double_load: DOUBLE_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 575 - r: FLOAT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 576 - r: FLOAT_LOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 577 - float_load: FLOAT_LOAD(riv, riv)
    EMIT_INSTRUCTION, // 578 - float_load: FLOAT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 579 - r: FLOAT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 580 - r: FLOAT_ALOAD(rlv, riv)
    EMIT_INSTRUCTION, // 581 - r: FLOAT_ALOAD(riv, r)
    EMIT_INSTRUCTION, // 582 - r: FLOAT_ALOAD(rlv, rlv)
    EMIT_INSTRUCTION, // 583 - float_load: FLOAT_ALOAD(riv, riv)
    EMIT_INSTRUCTION, // 584 - stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 585 - stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 586 - stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 587 - stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 588 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 589 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 590 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 591 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 592 - stm: DOUBLE_ASTORE(r, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 593 - stm: FLOAT_STORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 594 - stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 595 - stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 596 - stm: FLOAT_STORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 597 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 598 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 599 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, rlv))
    EMIT_INSTRUCTION, // 600 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, rlv))
    EMIT_INSTRUCTION, // 601 - stm: FLOAT_ASTORE(r, OTHER_OPERAND(r, r))
    EMIT_INSTRUCTION, // 602 - r: INT_2FLOAT(riv)
    EMIT_INSTRUCTION, // 603 - r: INT_2FLOAT(load32)
    EMIT_INSTRUCTION, // 604 - r: INT_2DOUBLE(riv)
    EMIT_INSTRUCTION, // 605 - r: INT_2DOUBLE(load32)
    EMIT_INSTRUCTION, // 606 - r: FLOAT_2DOUBLE(r)
    EMIT_INSTRUCTION, // 607 - r: FLOAT_2DOUBLE(float_load)
    EMIT_INSTRUCTION, // 608 - r: DOUBLE_2FLOAT(r)
    EMIT_INSTRUCTION, // 609 - r: DOUBLE_2FLOAT(double_load)
    EMIT_INSTRUCTION, // 610 - r: FLOAT_2INT(r)
    EMIT_INSTRUCTION, // 611 - r: FLOAT_2LONG(r)
    EMIT_INSTRUCTION, // 612 - r: DOUBLE_2INT(r)
    EMIT_INSTRUCTION, // 613 - r: DOUBLE_2LONG(r)
    EMIT_INSTRUCTION, // 614 - r: FLOAT_AS_INT_BITS(r)
    NOFLAGS, // 615 - load32: FLOAT_AS_INT_BITS(float_load)
    EMIT_INSTRUCTION, // 616 - r: DOUBLE_AS_LONG_BITS(r)
    NOFLAGS, // 617 - load64: DOUBLE_AS_LONG_BITS(double_load)
    EMIT_INSTRUCTION, // 618 - r: INT_BITS_AS_FLOAT(riv)
    NOFLAGS, // 619 - float_load: INT_BITS_AS_FLOAT(load32)
    EMIT_INSTRUCTION, // 620 - r: LONG_BITS_AS_DOUBLE(rlv)
    NOFLAGS, // 621 - double_load: LONG_BITS_AS_DOUBLE(load64)
    EMIT_INSTRUCTION, // 622 - r: MATERIALIZE_FP_CONSTANT(any)
    EMIT_INSTRUCTION, // 623 - float_load: MATERIALIZE_FP_CONSTANT(any)
    EMIT_INSTRUCTION, // 624 - double_load: MATERIALIZE_FP_CONSTANT(any)
    EMIT_INSTRUCTION, // 625 - stm: CLEAR_FLOATING_POINT_STATE
    EMIT_INSTRUCTION, // 626 - stm: FLOAT_IFCMP(r,r)
    EMIT_INSTRUCTION, // 627 - stm: FLOAT_IFCMP(r,float_load)
    EMIT_INSTRUCTION, // 628 - stm: FLOAT_IFCMP(float_load,r)
    EMIT_INSTRUCTION, // 629 - stm: DOUBLE_IFCMP(r,r)
    EMIT_INSTRUCTION, // 630 - stm: DOUBLE_IFCMP(r,double_load)
    EMIT_INSTRUCTION, // 631 - stm: DOUBLE_IFCMP(double_load,r)
    EMIT_INSTRUCTION, // 632 - r: FCMP_CMOV(r, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 633 - r: FCMP_CMOV(r, OTHER_OPERAND(float_load, any))
    EMIT_INSTRUCTION, // 634 - r: FCMP_CMOV(r, OTHER_OPERAND(double_load, any))
    EMIT_INSTRUCTION, // 635 - r: FCMP_CMOV(float_load, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 636 - r: FCMP_CMOV(double_load, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 637 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, any))
    EMIT_INSTRUCTION, // 638 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, float_load)))
    EMIT_INSTRUCTION, // 639 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, double_load)))
    EMIT_INSTRUCTION, // 640 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(float_load, r)))
    EMIT_INSTRUCTION, // 641 - r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(double_load, r)))
    EMIT_INSTRUCTION, // 642 - r: FCMP_FCMOV(r, OTHER_OPERAND(float_load, any))
    EMIT_INSTRUCTION, // 643 - r: FCMP_FCMOV(r, OTHER_OPERAND(double_load, any))
    EMIT_INSTRUCTION, // 644 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 645 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 646 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 647 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 648 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 649 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
    EMIT_INSTRUCTION, // 650 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 651 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
    EMIT_INSTRUCTION, // 652 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 653 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 654 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 655 - r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 656 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 657 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
    EMIT_INSTRUCTION, // 658 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 659 - r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
    EMIT_INSTRUCTION, // 660 - stm: LONG_ASTORE(load64, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 661 - stm: LONG_ASTORE(load64, OTHER_OPERAND(rlv, riv))
    EMIT_INSTRUCTION, // 662 - stm: LONG_STORE(load64, OTHER_OPERAND(riv, riv))
    EMIT_INSTRUCTION, // 663 - stm: LONG_STORE(load64, OTHER_OPERAND(rlv, riv))
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
   * address1scaledreg:	INT_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code87(AbstractBURS_TreeNode p) {
    pushAddress(null, Binary.getVal1(P(p)).asRegister(), LEA_SHIFT(Binary.getVal2(P(p))), Offset.zero());
  }

  /**
   * Emit code for rule number 88:
   * address1reg:	INT_ADD(r, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code88(AbstractBURS_TreeNode p) {
    pushAddress(R(Binary.getVal1(P(p))), null, B_S, Offset.fromLong(LV(Binary.getVal2(P(p)))));
  }

  /**
   * Emit code for rule number 89:
   * address1reg:	INT_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code89(AbstractBURS_TreeNode p) {
    pushAddress(R(Move.getVal(P(p))), null, B_S, Offset.zero());
  }

  /**
   * Emit code for rule number 90:
   * address:	INT_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code90(AbstractBURS_TreeNode p) {
    pushAddress(R(Binary.getVal1(P(p))), R(Binary.getVal2(P(p))), B_S, Offset.zero());
  }

  /**
   * Emit code for rule number 91:
   * address1reg:	INT_ADD(address1reg, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code91(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 92:
   * address1scaledreg:	INT_ADD(address1scaledreg, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code92(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 93:
   * address:	INT_ADD(r, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code93(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal1(P(p)));
  }

  /**
   * Emit code for rule number 94:
   * address:	INT_ADD(address1scaledreg, r)
   * @param p BURS node to apply the rule to
   */
  private void code94(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 95:
   * address:	INT_ADD(address1scaledreg, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code95(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 96:
   * address:	INT_ADD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code96(AbstractBURS_TreeNode p) {
    combineAddresses();
  }

  /**
   * Emit code for rule number 97:
   * address:	INT_ADD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code97(AbstractBURS_TreeNode p) {
    combineAddresses();
  }

  /**
   * Emit code for rule number 98:
   * address1scaledreg:	LONG_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code98(AbstractBURS_TreeNode p) {
    pushAddress(null, Binary.getVal1(P(p)).asRegister(), LEA_SHIFT(Binary.getVal2(P(p))), Offset.zero());
  }

  /**
   * Emit code for rule number 99:
   * address1reg:	LONG_ADD(r, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code99(AbstractBURS_TreeNode p) {
    pushAddress(R(Binary.getVal1(P(p))), null, B_S, Offset.fromLong(LV(Binary.getVal2(P(p)))));
  }

  /**
   * Emit code for rule number 100:
   * address1reg:	LONG_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code100(AbstractBURS_TreeNode p) {
    pushAddress(R(Move.getVal(P(p))), null, B_S, Offset.zero());
  }

  /**
   * Emit code for rule number 101:
   * address:	LONG_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code101(AbstractBURS_TreeNode p) {
    pushAddress(R(Binary.getVal1(P(p))), R(Binary.getVal2(P(p))), B_S, Offset.zero());
  }

  /**
   * Emit code for rule number 102:
   * address1reg:	LONG_ADD(address1reg, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code102(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 103:
   * address1scaledreg:	LONG_ADD(address1scaledreg, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code103(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 104:
   * address:	LONG_ADD(r, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code104(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal1(P(p)));
  }

  /**
   * Emit code for rule number 105:
   * address:	LONG_ADD(address1scaledreg, r)
   * @param p BURS node to apply the rule to
   */
  private void code105(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 106:
   * address:	LONG_ADD(address1scaledreg, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code106(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 107:
   * address:	LONG_ADD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code107(AbstractBURS_TreeNode p) {
    combineAddresses();
  }

  /**
   * Emit code for rule number 108:
   * address:	LONG_ADD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code108(AbstractBURS_TreeNode p) {
    combineAddresses();
  }

  /**
   * Emit code for rule number 109:
   * r:	ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code109(AbstractBURS_TreeNode p) {
    ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 110:
   * r:	ATTEMPT_INT(riv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code110(AbstractBURS_TreeNode p) {
    ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 111:
   * r:	ATTEMPT_INT(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code111(AbstractBURS_TreeNode p) {
    ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getOffset(P(p)), DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 112:
   * r:	ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code112(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 113:
   * r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code113(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 114:
   * r:	ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code114(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 115:
   * r:	ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code115(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 116:
   * r:	ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code116(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 117:
   * r:	ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv, riv)))
   * @param p BURS node to apply the rule to
   */
  private void code117(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(P(p))); 
ATTEMPT_INT(Attempt.getClearResult(P(p)), 
              consumeAddress(DW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 118:
   * stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code118(AbstractBURS_TreeNode p) {
    ATTEMPT_INT_IFCMP(MO(Attempt.getAddress(PL(p)), Attempt.getOffset(PL(p)), DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 119:
   * stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code119(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 120:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code120(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 121:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code121(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 122:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code122(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 123:
   * stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code123(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 124:
   * stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code124(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 125:
   * stm:	INT_IFCMP(ATTEMPT_INT(riv, OTHER_OPERAND(riv, OTHER_OPERAND(riv,riv))), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code125(AbstractBURS_TreeNode p) {
    ATTEMPT_INT_IFCMP(MO(Attempt.getAddress(PL(p)), Attempt.getOffset(PL(p)), DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 126:
   * stm:	INT_IFCMP(ATTEMPT_INT(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code126(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 127:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code127(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 128:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code128(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 129:
   * stm:	INT_IFCMP(ATTEMPT_INT(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code129(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 130:
   * stm:	INT_IFCMP(ATTEMPT_INT(address, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code130(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 131:
   * stm:	INT_IFCMP(ATTEMPT_INT(INT_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(riv,riv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code131(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getAddress(PL(p))); 
ATTEMPT_INT_IFCMP(consumeAddress(DW, Attempt.getLocation(PL(p)), Attempt.getGuard(PL(p))), 
	            Attempt.getOldValue(PL(p)), Attempt.getNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 132:
   * r:	ATTEMPT_LONG(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code132(AbstractBURS_TreeNode p) {
    ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              MO(Attempt.getClearAddress(P(p)), Attempt.getClearOffset(P(p)), QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 133:
   * r:	ATTEMPT_LONG(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code133(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(P(p))); 
ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              consumeAddress(QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 134:
   * r:	ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code134(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(P(p))); 
ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              consumeAddress(QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 135:
   * r:	ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code135(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              consumeAddress(QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 136:
   * r:	ATTEMPT_LONG(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code136(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              consumeAddress(QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 137:
   * r:	ATTEMPT_LONG(address, OTHER_OPERAND(LONG_CONSTANT, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code137(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(P(p))); 
ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              consumeAddress(QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 138:
   * r:	ATTEMPT_LONG(LONG_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(rlv, rlv)))
   * @param p BURS node to apply the rule to
   */
  private void code138(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(P(p))); 
ATTEMPT_LONG(Attempt.getClearResult(P(p)), 
              consumeAddress(QW, Attempt.getClearLocation(P(p)), Attempt.getClearGuard(P(p))), 
              Attempt.getClearOldValue(P(p)), Attempt.getClearNewValue(P(p)));
  }

  /**
   * Emit code for rule number 139:
   * stm:	INT_IFCMP(ATTEMPT_LONG(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code139(AbstractBURS_TreeNode p) {
    ATTEMPT_LONG_IFCMP(MO(Attempt.getClearAddress(PL(p)), Attempt.getOffset(PL(p)), QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 140:
   * stm:	INT_IFCMP(ATTEMPT_LONG(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code140(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 141:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code141(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 142:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code142(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 143:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code143(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 144:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address, OTHER_OPERAND(LONG_CONSTANT, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code144(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 145:
   * stm:	INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code145(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)).flipCode(), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 146:
   * stm:	INT_IFCMP(ATTEMPT_LONG(rlv, OTHER_OPERAND(rlv, OTHER_OPERAND(rlv,rlv))), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code146(AbstractBURS_TreeNode p) {
    ATTEMPT_LONG_IFCMP(MO(Attempt.getClearAddress(PL(p)), Attempt.getOffset(PL(p)), QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 147:
   * stm:	INT_IFCMP(ATTEMPT_LONG(r, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code147(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 148:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(r, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code148(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 149:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address1scaledreg, OTHER_OPERAND(address1reg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code149(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 150:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address1reg, OTHER_OPERAND(address1scaledreg, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code150(AbstractBURS_TreeNode p) {
    combineAddresses(); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 151:
   * stm:	INT_IFCMP(ATTEMPT_LONG(address, OTHER_OPERAND(LONG_CONSTANT, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code151(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getOffset(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 152:
   * stm:	INT_IFCMP(ATTEMPT_LONG(LONG_CONSTANT, OTHER_OPERAND(address, OTHER_OPERAND(rlv,rlv))),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code152(AbstractBURS_TreeNode p) {
    augmentAddress(Attempt.getClearAddress(PL(p))); 
ATTEMPT_LONG_IFCMP(consumeAddress(QW, Attempt.getClearLocation(PL(p)), Attempt.getClearGuard(PL(p))), 
	            Attempt.getClearOldValue(PL(p)), Attempt.getClearNewValue(PL(p)), 
		    IfCmp.getCond(P(p)), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p)));
  }

  /**
   * Emit code for rule number 153:
   * bittest:	INT_AND(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code153(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), Binary.getVal1(PLR(p)).copy()));
  }

  /**
   * Emit code for rule number 154:
   * bittest:	INT_AND(INT_USHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code154(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VLRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PLR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VLRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 155:
   * bittest:	INT_AND(INT_USHR(r,INT_CONSTANT),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code155(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), IC(VLR(p))));
  }

  /**
   * Emit code for rule number 156:
   * bittest:	INT_AND(INT_SHR(r,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code156(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), Binary.getVal1(PLR(p)).copy()));
  }

  /**
   * Emit code for rule number 157:
   * bittest:	INT_AND(INT_SHR(load32,INT_AND(r,INT_CONSTANT)),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code157(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VLRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PLR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VLRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 158:
   * bittest:	INT_AND(INT_SHR(r,INT_CONSTANT),INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code158(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(PL(p)).copy(), IC(VLR(p))));
  }

  /**
   * Emit code for rule number 159:
   * bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(riv,INT_CONSTANT)),r)
   * @param p BURS node to apply the rule to
   */
  private void code159(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal2(P(p)), Binary.getVal1(PLR(p)).copy()));
  }

  /**
   * Emit code for rule number 160:
   * bittest:	INT_AND(INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)),load32)
   * @param p BURS node to apply the rule to
   */
  private void code160(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VLRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PLR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VLRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 161:
   * bittest:	INT_AND(r,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code161(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_BT, Binary.getVal1(P(p)), Binary.getVal1(PRR(p)).copy()));
  }

  /**
   * Emit code for rule number 162:
   * bittest:	INT_AND(load32,INT_SHL(INT_CONSTANT,INT_AND(r, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code162(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
if (VM.VerifyAssertions) VM._assert((VRRR(p) & 0x7FFFFFFF) <= 31); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), Binary.getVal1(PRR(p))))); 
EMIT(CPOS(P(p), MIR_BinaryAcc.create(IA32_AND, new RegisterOperand(tmp, TypeReference.Int), IC(VRRR(p))))); 
EMIT(MIR_Test.mutate(P(p), IA32_BT, consumeMO(), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 163:
   * r:	BOOLEAN_CMP_INT(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code163(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), 
   BooleanCmp.getClearVal1(P(p)), BooleanCmp.getClearVal2(P(p)), 
   BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 164:
   * boolcmp: BOOLEAN_CMP_INT(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code164(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, BooleanCmp.getClearVal1(P(p)), BooleanCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 165:
   * r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code165(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p),MIR_Test.create(IA32_TEST, BooleanCmp.getVal1(P(p)).copy(), BooleanCmp.getClearVal1(P(p)))));
BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 166:
   * boolcmp: BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code166(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p))); 
EMIT(CPOS(P(p),MIR_Test.create(IA32_TEST, BooleanCmp.getVal1(P(p)).copy(), BooleanCmp.getClearVal1(P(p)))));
  }

  /**
   * Emit code for rule number 167:
   * r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code167(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SHR, P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getClearVal1(P(p)), IC(31));
  }

  /**
   * Emit code for rule number 168:
   * r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code168(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SHR, P(p), BooleanCmp.getResult(P(p)), consumeMO(), IC(31));
  }

  /**
   * Emit code for rule number 169:
   * r:	BOOLEAN_CMP_INT(r,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code169(AbstractBURS_TreeNode p) {
    RegisterOperand result = BooleanCmp.getResult(P(p)); 
EMIT_Commutative(IA32_SHR, P(p), result, BooleanCmp.getClearVal1(P(p)), IC(31)); 
EMIT(CPOS(P(p),MIR_BinaryAcc.create(IA32_XOR, result.copyRO(), IC(1))));
  }

  /**
   * Emit code for rule number 170:
   * r:	BOOLEAN_CMP_INT(load32,INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code170(AbstractBURS_TreeNode p) {
    RegisterOperand result = BooleanCmp.getResult(P(p)); 
EMIT_Commutative(IA32_SHR, P(p), result, consumeMO(), IC(31)); 
EMIT(CPOS(P(p),MIR_BinaryAcc.create(IA32_XOR, result.copyRO(), IC(1))));
  }

  /**
   * Emit code for rule number 171:
   * r:	BOOLEAN_CMP_INT(cz, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code171(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 172:
   * boolcmp: BOOLEAN_CMP_INT(cz, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code172(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 173:
   * r:	BOOLEAN_CMP_INT(szp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code173(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 174:
   * boolcmp: BOOLEAN_CMP_INT(szp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code174(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 175:
   * r:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code175(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), BIT_TEST(VR(p),BooleanCmp.getCond(P(p))));
  }

  /**
   * Emit code for rule number 176:
   * boolcmp:	BOOLEAN_CMP_INT(bittest, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code176(AbstractBURS_TreeNode p) {
    pushCOND(BIT_TEST(VR(p),BooleanCmp.getCond(P(p))));
  }

  /**
   * Emit code for rule number 177:
   * r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code177(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), consumeCOND());
  }

  /**
   * Emit code for rule number 179:
   * r:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code179(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getResult(P(p)), consumeCOND().flipCode());
  }

  /**
   * Emit code for rule number 180:
   * boolcmp:	BOOLEAN_CMP_INT(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code180(AbstractBURS_TreeNode p) {
    pushCOND(consumeCOND().flipCode()); // invert already pushed condition
  }

  /**
   * Emit code for rule number 181:
   * r:	BOOLEAN_CMP_INT(load32,riv)
   * @param p BURS node to apply the rule to
   */
  private void code181(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(PL(p), BooleanCmp.getClearResult(P(p)), 
            consumeMO(), BooleanCmp.getClearVal2(P(p)), 
	    BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 182:
   * boolcmp: BOOLEAN_CMP_INT(load32,riv)
   * @param p BURS node to apply the rule to
   */
  private void code182(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, consumeMO(), BooleanCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 183:
   * r:	BOOLEAN_CMP_INT(r,load32)
   * @param p BURS node to apply the rule to
   */
  private void code183(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(PR(p), BooleanCmp.getClearResult(P(p)), 
            BooleanCmp.getClearVal1(P(p)), consumeMO(), 
	    BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 184:
   * boolcmp: BOOLEAN_CMP_INT(riv,load32)
   * @param p BURS node to apply the rule to
   */
  private void code184(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, BooleanCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 185:
   * stm:	BYTE_STORE(boolcmp, OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code185(AbstractBURS_TreeNode p) {
    EMIT(MIR_Set.mutate(P(p), IA32_SET__B, MO_S(P(p),B), COND(consumeCOND())));
  }

  /**
   * Emit code for rule number 186:
   * stm:	BYTE_ASTORE(boolcmp, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code186(AbstractBURS_TreeNode p) {
    EMIT(MIR_Set.mutate(P(p), IA32_SET__B, MO_AS(P(p),B_S,B), COND(consumeCOND())));
  }

  /**
   * Emit code for rule number 187:
   * r:	BOOLEAN_CMP_LONG(r,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code187(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getClearResult(P(p)), 
   BooleanCmp.getClearVal1(P(p)), BooleanCmp.getClearVal2(P(p)), 
   BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 188:
   * boolcmp: BOOLEAN_CMP_LONG(r,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code188(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, BooleanCmp.getClearVal1(P(p)), BooleanCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 189:
   * r:	BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code189(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p),MIR_Test.create(IA32_TEST, BooleanCmp.getVal1(P(p)).copy(), BooleanCmp.getClearVal1(P(p)))));
BOOLEAN_CMP_INT(P(p), BooleanCmp.getClearResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 190:
   * boolcmp: BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code190(AbstractBURS_TreeNode p) {
    pushCOND(BooleanCmp.getCond(P(p))); 
EMIT(CPOS(P(p),MIR_Test.create(IA32_TEST, BooleanCmp.getVal1(P(p)).copy(), BooleanCmp.getClearVal1(P(p)))));
  }

  /**
   * Emit code for rule number 191:
   * r:	BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code191(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SHR, P(p), BooleanCmp.getClearResult(P(p)), BooleanCmp.getClearVal1(P(p)), IC(63));
  }

  /**
   * Emit code for rule number 192:
   * r:	BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code192(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SHR, P(p), BooleanCmp.getClearResult(P(p)), consumeMO(), IC(63));
  }

  /**
   * Emit code for rule number 193:
   * r:	BOOLEAN_CMP_LONG(r,LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code193(AbstractBURS_TreeNode p) {
    RegisterOperand result = BooleanCmp.getClearResult(P(p)); 
EMIT_Commutative(IA32_SHR, P(p), result, BooleanCmp.getClearVal1(P(p)), IC(63)); 
EMIT(CPOS(P(p),MIR_BinaryAcc.create(IA32_XOR, result.copyRO(), IC(1))));
  }

  /**
   * Emit code for rule number 194:
   * r:	BOOLEAN_CMP_LONG(load64,LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code194(AbstractBURS_TreeNode p) {
    RegisterOperand result = BooleanCmp.getClearResult(P(p)); 
EMIT_Commutative(IA32_SHR, P(p), result, consumeMO(), IC(63)); 
EMIT(CPOS(P(p),MIR_BinaryAcc.create(IA32_XOR, result.copyRO(), IC(1))));
  }

  /**
   * Emit code for rule number 195:
   * r:	BOOLEAN_CMP_LONG(cz, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code195(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(P(p), BooleanCmp.getClearResult(P(p)), BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 196:
   * r:	BOOLEAN_CMP_LONG(load64,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code196(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(PL(p), BooleanCmp.getClearResult(P(p)), 
            consumeMO(), BooleanCmp.getClearVal2(P(p)), 
	    BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 197:
   * boolcmp: BOOLEAN_CMP_LONG(load64,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code197(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, consumeMO(), BooleanCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 198:
   * r:	BOOLEAN_CMP_LONG(r,load64)
   * @param p BURS node to apply the rule to
   */
  private void code198(AbstractBURS_TreeNode p) {
    BOOLEAN_CMP_INT(PR(p), BooleanCmp.getClearResult(P(p)), 
            BooleanCmp.getClearVal1(P(p)), consumeMO(), 
	    BooleanCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 199:
   * boolcmp: BOOLEAN_CMP_LONG(rlv,load64)
   * @param p BURS node to apply the rule to
   */
  private void code199(AbstractBURS_TreeNode p) {
    ConditionOperand cond = BooleanCmp.getCond(P(p)); 
pushCOND(cond); 
EMIT_Compare(P(p), cond, BooleanCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 200:
   * r:	BOOLEAN_NOT(r)
   * @param p BURS node to apply the rule to
   */
  private void code200(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)), IC(1));
  }

  /**
   * Emit code for rule number 201:
   * stm:	BYTE_STORE(BOOLEAN_NOT(UBYTE_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code201(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), B), MO_S(P(p), B), IC(1));
  }

  /**
   * Emit code for rule number 202:
   * stm:	BYTE_ASTORE(BOOLEAN_NOT(UBYTE_ALOAD(rlv,riv)),OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code202(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), B_S, B), MO_AS(P(p), B_S, B), IC(1));
  }

  /**
   * Emit code for rule number 203:
   * stm:    BYTE_STORE(riv, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code203(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), B), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 204:
   * stm:    BYTE_STORE(load8, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code204(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
EMIT(CPOS(PL(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), consumeMO()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), B), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 205:
   * stm:    BYTE_ASTORE(riv, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code205(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), B_S, B), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 206:
   * stm:    BYTE_ASTORE(load8, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code206(AbstractBURS_TreeNode p) {
    Register tmp = regpool.getInteger(); 
EMIT(CPOS(PL(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Int), consumeMO()))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), B_S, B), new RegisterOperand(tmp, TypeReference.Int)));
  }

  /**
   * Emit code for rule number 207:
   * r: CMP_CMOV(r, OTHER_OPERAND(riv, any))
   * @param p BURS node to apply the rule to
   */
  private void code207(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP,  CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 208:
   * r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code208(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Test.create(IA32_TEST, CondMove.getVal1(P(p)).copy(), CondMove.getClearVal1(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 209:
   * r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code209(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SAR, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), IC(31));
  }

  /**
   * Emit code for rule number 210:
   * r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code210(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_SAR, P(p), CondMove.getClearResult(P(p)), consumeMO(), IC(31));
  }

  /**
   * Emit code for rule number 211:
   * r: CMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code211(AbstractBURS_TreeNode p) {
    RegisterOperand result = CondMove.getClearResult(P(p)); 
EMIT_Commutative(IA32_SAR, P(p), result, CondMove.getClearVal1(P(p)), IC(31)); 
EMIT(CPOS(P(p),MIR_UnaryAcc.create(IA32_NOT, result.copyRO())));
  }

  /**
   * Emit code for rule number 212:
   * r: CMP_CMOV(load32, OTHER_OPERAND(INT_CONSTANT, OTHER_OPERAND(INT_CONSTANT, INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code212(AbstractBURS_TreeNode p) {
    RegisterOperand result = CondMove.getClearResult(P(p)); 
EMIT_Commutative(IA32_SAR, P(p), result, consumeMO(), IC(31)); 
EMIT(CPOS(P(p),MIR_UnaryAcc.create(IA32_NOT, result.copyRO())));
  }

  /**
   * Emit code for rule number 213:
   * r: CMP_CMOV(load8, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code213(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 214:
   * r: CMP_CMOV(uload8, OTHER_OPERAND(riv, any))
   * @param p BURS node to apply the rule to
   */
  private void code214(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 215:
   * r: CMP_CMOV(riv, OTHER_OPERAND(uload8, any))
   * @param p BURS node to apply the rule to
   */
  private void code215(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 216:
   * r: CMP_CMOV(sload16, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code216(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 217:
   * r: CMP_CMOV(load32, OTHER_OPERAND(riv, any))
   * @param p BURS node to apply the rule to
   */
  private void code217(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 218:
   * r: CMP_CMOV(riv, OTHER_OPERAND(load32, any))
   * @param p BURS node to apply the rule to
   */
  private void code218(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal1(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).flipOperands(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 219:
   * r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code219(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), consumeCOND(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 220:
   * r: CMP_CMOV(boolcmp, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code220(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), consumeCOND().flipCode(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 221:
   * r: CMP_CMOV(bittest, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code221(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), BIT_TEST(VRL(p), CondMove.getClearCond(P(p))), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 222:
   * r: CMP_CMOV(cz, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code222(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 223:
   * r: CMP_CMOV(szp, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code223(AbstractBURS_TreeNode p) {
    CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 224:
   * r:	INT_2BYTE(r)
   * @param p BURS node to apply the rule to
   */
  private void code224(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Unary.getResult(P(p)), Unary.getVal(P(p))));
  }

  /**
   * Emit code for rule number 225:
   * r:	INT_2BYTE(load8_16_32)
   * @param p BURS node to apply the rule to
   */
  private void code225(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Unary.getResult(P(p)), consumeMO()));
  }

  /**
   * Emit code for rule number 226:
   * stm:	BYTE_STORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code226(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), B), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 227:
   * stm:	BYTE_ASTORE(INT_2BYTE(r),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code227(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), B_S, B), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 228:
   * r:	INT_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code228(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)), true);
  }

  /**
   * Emit code for rule number 229:
   * r:	INT_2LONG(load32)
   * @param p BURS node to apply the rule to
   */
  private void code229(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), consumeMO(), true);
  }

  /**
   * Emit code for rule number 230:
   * r:      LONG_AND(INT_2LONG(r), LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code230(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Binary.getClearResult(P(p)), Unary.getClearVal(PL(p)), false);
  }

  /**
   * Emit code for rule number 231:
   * r:      LONG_AND(INT_2LONG(load32), LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code231(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Binary.getClearResult(P(p)), consumeMO(), false);
  }

  /**
   * Emit code for rule number 232:
   * r:	INT_2ADDRZerExt(r)
   * @param p BURS node to apply the rule to
   */
  private void code232(AbstractBURS_TreeNode p) {
    INT_2LONG(P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)), false);
  }

  /**
   * Emit code for rule number 233:
   * r:	INT_2SHORT(r)
   * @param p BURS node to apply the rule to
   */
  private void code233(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, Unary.getResult(P(p)), Unary.getVal(P(p)))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSXQ__W, Unary.getResult(P(p)), Unary.getVal(P(p)))); 
}
  }

  /**
   * Emit code for rule number 234:
   * r:	INT_2SHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code234(AbstractBURS_TreeNode p) {
    if (VM.BuildFor32Addr) { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, Unary.getResult(P(p)), setSize(consumeMO(), 2))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSXQ__W, Unary.getResult(P(p)), setSize(consumeMO(), 2))); 
}
  }

  /**
   * Emit code for rule number 235:
   * sload16:	INT_2SHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code235(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(),2));
  }

  /**
   * Emit code for rule number 236:
   * stm:	SHORT_STORE(INT_2SHORT(r), OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code236(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 237:
   * stm:	SHORT_ASTORE(INT_2SHORT(r), OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code237(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 238:
   * szpr:	INT_2USHORT(r)
   * @param p BURS node to apply the rule to
   */
  private void code238(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, Unary.getResult(P(p)).copyRO(), Unary.getClearVal(P(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_AND, Unary.getResult(P(p)), IC(0xFFFF)));
  }

  /**
   * Emit code for rule number 239:
   * uload16:	INT_2USHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code239(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(),2));
  }

  /**
   * Emit code for rule number 240:
   * r:	INT_2USHORT(load16_32)
   * @param p BURS node to apply the rule to
   */
  private void code240(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, Unary.getResult(P(p)), setSize(consumeMO(),2)));
  }

  /**
   * Emit code for rule number 241:
   * stm:	SHORT_STORE(INT_2USHORT(r), OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code241(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 242:
   * stm:	SHORT_ASTORE(INT_2USHORT(r), OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code242(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_AS(P(p), W_S, W), Unary.getClearVal(PL(p))));
  }

  /**
   * Emit code for rule number 243:
   * czr:	INT_ADD(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code243(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 244:
   * r:	INT_ADD(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code244(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isIntConstant()) { 
 pushAddress(R(Binary.getClearVal1(P(p))), null, B_S, Offset.fromIntSignExtend(VR(p))); 
} else { 
 pushAddress(R(Binary.getClearVal1(P(p))), R(Binary.getClearVal2(P(p))), B_S, Offset.zero()); 
} 
EMIT_Lea(P(p), Binary.getClearResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 245:
   * czr:	INT_ADD(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code245(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 246:
   * czr:	INT_ADD(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code246(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 247:
   * stm:	INT_STORE(INT_ADD(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code247(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 248:
   * stm:	INT_STORE(INT_ADD(riv,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code248(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 249:
   * stm:	INT_ASTORE(INT_ADD(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code249(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 250:
   * stm:	INT_ASTORE(INT_ADD(riv,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code250(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 251:
   * szpr:	INT_AND(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code251(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 252:
   * szp:	INT_AND(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code252(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))));
  }

  /**
   * Emit code for rule number 253:
   * szpr:	INT_AND(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code253(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 254:
   * szpr:	INT_AND(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code254(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 255:
   * szp:	INT_AND(load8_16_32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code255(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, consumeMO(), Binary.getClearVal2(P(p))));
  }

  /**
   * Emit code for rule number 256:
   * szp:	INT_AND(r, load8_16_32)
   * @param p BURS node to apply the rule to
   */
  private void code256(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, consumeMO(), Binary.getClearVal1(P(p))));
  }

  /**
   * Emit code for rule number 257:
   * stm:	INT_STORE(INT_AND(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code257(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 258:
   * stm:	INT_STORE(INT_AND(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code258(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 259:
   * stm:	INT_ASTORE(INT_AND(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code259(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 260:
   * stm:	INT_ASTORE(INT_AND(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code260(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 261:
   * r:	INT_DIV(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code261(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), true, true);
  }

  /**
   * Emit code for rule number 262:
   * r:	INT_DIV(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code262(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            consumeMO(), true, true);
  }

  /**
   * Emit code for rule number 263:
   * r:     UNSIGNED_DIV_64_32(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code263(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            GuardedBinary.getVal2(P(p)), true, false);
  }

  /**
   * Emit code for rule number 264:
   * r:     UNSIGNED_DIV_64_32(rlv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code264(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            consumeMO(), true, false);
  }

  /**
   * Emit code for rule number 265:
   * stm:	INT_IFCMP(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code265(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 266:
   * stm:	INT_IFCMP(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code266(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Test.create(IA32_TEST, IfCmp.getVal1(P(p)).copy(), IfCmp.getClearVal1(P(p))))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 267:
   * stm:	INT_IFCMP(load8, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code267(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 268:
   * stm:	INT_IFCMP(uload8, r)
   * @param p BURS node to apply the rule to
   */
  private void code268(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 269:
   * stm:	INT_IFCMP(r, uload8)
   * @param p BURS node to apply the rule to
   */
  private void code269(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), consumeMO(), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 270:
   * stm:	INT_IFCMP(sload16, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code270(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 271:
   * stm:	INT_IFCMP(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code271(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), consumeMO(), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 272:
   * stm:	INT_IFCMP(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code272(AbstractBURS_TreeNode p) {
    IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), consumeMO(), IfCmp.getCond(P(p)));
  }

  /**
   * Emit code for rule number 273:
   * stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code273(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(consumeCOND()), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 274:
   * stm:	INT_IFCMP(boolcmp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code274(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(consumeCOND().flipCode()), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 275:
   * stm:	INT_IFCMP(cz, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code275(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 276:
   * stm:	INT_IFCMP(szp, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code276(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 277:
   * stm:	INT_IFCMP(bittest, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code277(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(BIT_TEST(VR(p), IfCmp.getCond(P(p)))), IfCmp.getTarget(P(p)), IfCmp.getBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 278:
   * stm:	INT_IFCMP2(r,riv)
   * @param p BURS node to apply the rule to
   */
  private void code278(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp2.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, IfCmp2.getClearVal1(P(p)), IfCmp2.getClearVal2(P(p))))); 
EMIT(MIR_CondBranch2.mutate(P(p), IA32_JCC2,                                  
	                    COND(IfCmp2.getCond1(P(p))), IfCmp2.getClearTarget1(P(p)),IfCmp2.getClearBranchProfile1(P(p)), 
	                    COND(IfCmp2.getCond2(P(p))), IfCmp2.getClearTarget2(P(p)), IfCmp2.getClearBranchProfile2(P(p))));
  }

  /**
   * Emit code for rule number 279:
   * stm:	INT_IFCMP2(load32,riv)
   * @param p BURS node to apply the rule to
   */
  private void code279(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp2.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), IfCmp2.getClearVal2(P(p))))); 
EMIT(MIR_CondBranch2.mutate(P(p), IA32_JCC2,                                  
	                    COND(IfCmp2.getCond1(P(p))), IfCmp2.getClearTarget1(P(p)),IfCmp2.getClearBranchProfile1(P(p)), 
	                    COND(IfCmp2.getCond2(P(p))), IfCmp2.getClearTarget2(P(p)), IfCmp2.getClearBranchProfile2(P(p))));
  }

  /**
   * Emit code for rule number 280:
   * stm:	INT_IFCMP2(riv,load32)
   * @param p BURS node to apply the rule to
   */
  private void code280(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp2.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), IfCmp2.getClearVal1(P(p))))); 
EMIT(MIR_CondBranch2.mutate(P(p), IA32_JCC2,                                  
	                    COND(IfCmp2.getCond1(P(p)).flipOperands()), IfCmp2.getClearTarget1(P(p)),IfCmp2.getClearBranchProfile1(P(p)), 
	                    COND(IfCmp2.getCond2(P(p)).flipOperands()), IfCmp2.getClearTarget2(P(p)), IfCmp2.getClearBranchProfile2(P(p))));
  }

  /**
   * Emit code for rule number 281:
   * r:	INT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code281(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 282:
   * r:	INT_LOAD(rlv, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code282(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getAddress(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
		     consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 283:
   * r:	INT_LOAD(address1scaledreg, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code283(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 284:
   * r:	INT_LOAD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code284(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 285:
   * r:	INT_LOAD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code285(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 286:
   * r:	INT_LOAD(address, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code286(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(DW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 287:
   * r:      INT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code287(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 288:
   * r:	INT_MOVE(riv)
   * @param p BURS node to apply the rule to
   */
  private void code288(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 289:
   * czr:	INT_MOVE(czr)
   * @param p BURS node to apply the rule to
   */
  private void code289(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 291:
   * szpr:	INT_MOVE(szpr)
   * @param p BURS node to apply the rule to
   */
  private void code291(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 300:
   * r:	INT_MUL(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code300(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 301:
   * r:	INT_MUL(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code301(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 302:
   * r:	INT_MUL(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code302(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 303:
   * szpr:	INT_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code303(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 304:
   * stm:	INT_STORE(INT_NEG(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code304(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), MO_S(P(p), DW), MO_S(P(p), DW));
  }

  /**
   * Emit code for rule number 305:
   * stm:	INT_ASTORE(INT_NEG(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code305(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 306:
   * r:	INT_NOT(r)
   * @param p BURS node to apply the rule to
   */
  private void code306(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 307:
   * stm:	INT_STORE(INT_NOT(INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code307(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), MO_S(P(p), DW), MO_S(P(p), DW));
  }

  /**
   * Emit code for rule number 308:
   * stm:	INT_ASTORE(INT_NOT(INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code308(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 309:
   * szpr:	INT_OR(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code309(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 310:
   * szpr:	INT_OR(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code310(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 311:
   * szpr:	INT_OR(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code311(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 312:
   * stm:	INT_STORE(INT_OR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code312(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 313:
   * stm:	INT_STORE(INT_OR(r, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code313(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 314:
   * stm:	INT_ASTORE(INT_OR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code314(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 315:
   * stm:	INT_ASTORE(INT_OR(r, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code315(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 316:
   * r:	INT_REM(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code316(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
	    GuardedBinary.getClearVal2(P(p)), false, true);
  }

  /**
   * Emit code for rule number 317:
   * r:	INT_REM(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code317(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            consumeMO(), false, true);
  }

  /**
   * Emit code for rule number 318:
   * r:     UNSIGNED_REM_64_32(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code318(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            GuardedBinary.getVal2(P(p)), false, false);
  }

  /**
   * Emit code for rule number 319:
   * r:     UNSIGNED_REM_64_32(rlv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code319(AbstractBURS_TreeNode p) {
    INT_DIVIDES(P(p), GuardedBinary.getResult(P(p)), GuardedBinary.getVal1(P(p)), 
            consumeMO(), false, false);
  }

  /**
   * Emit code for rule number 320:
   * r:	INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code320(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(VLR(p)&0x1f));
  }

  /**
   * Emit code for rule number 321:
   * r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code321(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(VRR(p)&0x1f));
  }

  /**
   * Emit code for rule number 322:
   * r:      INT_OR(INT_SHL(r,INT_CONSTANT),INT_USHR(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code322(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(1));
  }

  /**
   * Emit code for rule number 323:
   * r:      INT_OR(INT_USHR(r,INT_CONSTANT),INT_SHL(r,INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code323(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(1));
  }

  /**
   * Emit code for rule number 324:
   * r:      INT_OR(INT_SHL(r,INT_AND(r,INT_CONSTANT)),INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code324(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 325:
   * r:      INT_OR(INT_USHR(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_SHL(r,INT_AND(r,INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code325(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PRR(p))))); 
EMIT_NonCommutative(IA32_ROL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 326:
   * r:      INT_OR(INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)),INT_USHR(r,INT_AND(r,INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code326(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PRR(p))))); 
EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 327:
   * r:      INT_OR(INT_USHR(r,INT_AND(r,INT_CONSTANT)),INT_SHL(r,INT_AND(INT_NEG(r),INT_CONSTANT)))
   * @param p BURS node to apply the rule to
   */
  private void code327(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT_NonCommutative(IA32_ROR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 328:
   * szpr:	INT_SHL(riv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code328(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 329:
   * szpr:	INT_SHL(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code329(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 330:
   * szpr:	INT_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code330(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 31); if(Binary.getVal2(P(p)).asIntConstant().value == 1) { 
 EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getVal1(P(p)).copy(), Binary.getClearVal1(P(p))); 
} else { 
 EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 331:
   * r:	INT_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code331(AbstractBURS_TreeNode p) {
    pushAddress(null, Binary.getClearVal1(P(p)).asRegister(), LEA_SHIFT(Binary.getClearVal2(P(p))), Offset.zero()); 
EMIT_Lea(P(p), Binary.getClearResult(P(p)), consumeAddress(DW, null, null));
  }

  /**
   * Emit code for rule number 332:
   * szpr:	INT_SHL(INT_SHR(r, INT_CONSTANT), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code332(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(0xffffffff << VR(p)));
  }

  /**
   * Emit code for rule number 333:
   * stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code333(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_S(P(p), DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 334:
   * stm:	INT_STORE(INT_SHL(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code334(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 31); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 335:
   * stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code335(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_AS(P(p), DW_S, DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 336:
   * stm:	INT_ASTORE(INT_SHL(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code336(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 337:
   * szpr:	INT_SHR(riv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code337(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 338:
   * szpr:	INT_SHR(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code338(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 339:
   * szpr:	INT_SHR(riv, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code339(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 31); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 340:
   * stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code340(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_S(P(p), DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 341:
   * stm:	INT_STORE(INT_SHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code341(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 31); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 342:
   * stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code342(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_AS(P(p), DW_S, DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 343:
   * stm:	INT_ASTORE(INT_SHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code343(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 344:
   * stm:	INT_STORE(riv, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code344(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 345:
   * stm:	INT_STORE(riv, OTHER_OPERAND(rlv, address1scaledreg))
   * @param p BURS node to apply the rule to
   */
  private void code345(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getAddress(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, 
                     consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 346:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code346(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, 
                     consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 347:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address1scaledreg, address1reg))
   * @param p BURS node to apply the rule to
   */
  private void code347(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
                    consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
                    Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 348:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address1reg, address1scaledreg))
   * @param p BURS node to apply the rule to
   */
  private void code348(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
                    consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
                    Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 349:
   * stm:	INT_STORE(riv, OTHER_OPERAND(address, LONG_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code349(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
	             consumeAddress(DW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 350:
   * czr:	INT_SUB(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code350(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 351:
   * r:	INT_SUB(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code351(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, Binary.getResult(P(p)).copy()))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, Binary.getResult(P(p)), Binary.getVal1(P(p))));
  }

  /**
   * Emit code for rule number 352:
   * r:	INT_SUB(load32, r)
   * @param p BURS node to apply the rule to
   */
  private void code352(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, Binary.getResult(P(p)).copy()))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, Binary.getResult(P(p)), consumeMO()));
  }

  /**
   * Emit code for rule number 353:
   * czr:	INT_SUB(riv, load32)
   * @param p BURS node to apply the rule to
   */
  private void code353(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 354:
   * czr:	INT_SUB(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code354(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getResult(P(p)), consumeMO(), Binary.getVal2(P(p)));
  }

  /**
   * Emit code for rule number 355:
   * stm:	INT_STORE(INT_SUB(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code355(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SUB, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 356:
   * stm:	INT_STORE(INT_SUB(riv, INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code356(AbstractBURS_TreeNode p) {
    MemoryOperand result = MO_S(P(p), DW); 
EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, result))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, result.copy(), Binary.getClearVal1(PL(p))));
  }

  /**
   * Emit code for rule number 357:
   * stm:	INT_ASTORE(INT_SUB(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code357(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SUB, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 358:
   * stm:	INT_ASTORE(INT_SUB(riv, INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code358(AbstractBURS_TreeNode p) {
    MemoryOperand result = MO_AS(P(p), DW_S, DW); 
EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, result))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, result.copy(), Binary.getClearVal1(PL(p))));
  }

  /**
   * Emit code for rule number 359:
   * szpr:	INT_USHR(riv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code359(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 360:
   * szpr:	INT_USHR(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code360(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 361:
   * szpr:	INT_USHR(riv, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code361(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 31); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 362:
   * stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code362(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_S(P(p), DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 363:
   * stm:	INT_STORE(INT_USHR(INT_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code363(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 31); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_S(P(p), DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 364:
   * stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code364(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_AS(P(p), DW_S, DW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 365:
   * stm:	INT_ASTORE(INT_USHR(INT_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code365(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 366:
   * szpr:	INT_XOR(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code366(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 367:
   * szpr:	INT_XOR(r, load32)
   * @param p BURS node to apply the rule to
   */
  private void code367(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 368:
   * szpr:	INT_XOR(load32, riv)
   * @param p BURS node to apply the rule to
   */
  private void code368(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO() );
  }

  /**
   * Emit code for rule number 369:
   * stm:	INT_STORE(INT_XOR(INT_LOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code369(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 370:
   * stm:	INT_STORE(INT_XOR(r,INT_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code370(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), DW), MO_S(P(p), DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 371:
   * stm:	INT_ASTORE(INT_XOR(INT_ALOAD(riv,riv),riv),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code371(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 372:
   * stm:	INT_ASTORE(INT_XOR(r,INT_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code372(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), DW_S, DW), MO_AS(P(p), DW_S, DW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 373:
   * r: LCMP_CMOV(r, OTHER_OPERAND(rlv, any))
   * @param p BURS node to apply the rule to
   */
  private void code373(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP,  CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 374:
   * r: LCMP_CMOV(r, OTHER_OPERAND(INT_CONSTANT, any))
   * @param p BURS node to apply the rule to
   */
  private void code374(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Test.create(IA32_TEST, CondMove.getClearVal1(P(p)), CondMove.getClearVal1(P(p)).copy()))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 375:
   * r: LCMP_CMOV(load64, OTHER_OPERAND(rlv, any))
   * @param p BURS node to apply the rule to
   */
  private void code375(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getClearVal2(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 376:
   * r: LCMP_CMOV(rlv, OTHER_OPERAND(load64, any))
   * @param p BURS node to apply the rule to
   */
  private void code376(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_CMP, consumeMO(), CondMove.getVal1(P(p))))); 
CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).flipOperands(), 
         CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 377:
   * r:	LONG_ADD(address1scaledreg, r)
   * @param p BURS node to apply the rule to
   */
  private void code377(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p))); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 378:
   * r:	LONG_ADD(r, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code378(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal1(P(p))); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 379:
   * r:	LONG_ADD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code379(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 380:
   * r:	LONG_ADD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code380(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 381:
   * r:	LONG_ADD(address, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code381(AbstractBURS_TreeNode p) {
    augmentAddress(Binary.getVal2(P(p))); 
EMIT_Lea(P(p), Binary.getResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 382:
   * r:	LONG_MOVE(address)
   * @param p BURS node to apply the rule to
   */
  private void code382(AbstractBURS_TreeNode p) {
    EMIT_Lea(P(p), Move.getResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 383:
   * r:      BYTE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code383(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, Load.getResult(P(p)), MO_L(P(p), B)));
  }

  /**
   * Emit code for rule number 384:
   * sload8:	BYTE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code384(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), B));
  }

  /**
   * Emit code for rule number 385:
   * r:      BYTE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code385(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B)));
  }

  /**
   * Emit code for rule number 386:
   * r:      BYTE_ALOAD(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code386(AbstractBURS_TreeNode p) {
    RegisterOperand index = ALoad.getIndex(P(p)).asRegister(); 
if (index.getRegister().isInteger()) { 
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B))); 
}
  }

  /**
   * Emit code for rule number 387:
   * sload8:	BYTE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code387(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), B_S, B));
  }

  /**
   * Emit code for rule number 388:
   * r:      UBYTE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code388(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, Load.getResult(P(p)), MO_L(P(p), B)));
  }

  /**
   * Emit code for rule number 389:
   * uload8:	UBYTE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code389(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), B));
  }

  /**
   * Emit code for rule number 390:
   * r:	UBYTE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code390(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B)));
  }

  /**
   * Emit code for rule number 391:
   * r:      UBYTE_ALOAD(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code391(AbstractBURS_TreeNode p) {
    RegisterOperand index = ALoad.getIndex(P(p)).asRegister(); 
if (index.getRegister().isInteger()) { 
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__B, ALoad.getResult(P(p)), MO_AL(P(p), B_S, B))); 
}
  }

  /**
   * Emit code for rule number 392:
   * uload8:	UBYTE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code392(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), B_S, B));
  }

  /**
   * Emit code for rule number 395:
   * r:      SHORT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code395(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, Load.getResult(P(p)), MO_L(P(p), W)));
  }

  /**
   * Emit code for rule number 396:
   * sload16: SHORT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code396(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), W));
  }

  /**
   * Emit code for rule number 397:
   * r:      SHORT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code397(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W)));
  }

  /**
   * Emit code for rule number 398:
   * r:      SHORT_ALOAD(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code398(AbstractBURS_TreeNode p) {
    RegisterOperand index = ALoad.getIndex(P(p)).asRegister(); 
if (index.getRegister().isInteger()) { 
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVSX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W))); 
}
  }

  /**
   * Emit code for rule number 399:
   * sload16: SHORT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code399(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), W_S, W));
  }

  /**
   * Emit code for rule number 400:
   * r:      USHORT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code400(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, Load.getResult(P(p)), MO_L(P(p), W)));
  }

  /**
   * Emit code for rule number 401:
   * uload16: USHORT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code401(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), W));
  }

  /**
   * Emit code for rule number 402:
   * r:      USHORT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code402(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W)));
  }

  /**
   * Emit code for rule number 403:
   * r:      USHORT_ALOAD(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code403(AbstractBURS_TreeNode p) {
    RegisterOperand index = ALoad.getIndex(P(p)).asRegister(); 
if (index.getRegister().isInteger()) { 
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W))); 
} else { 
EMIT(MIR_Unary.mutate(P(p), IA32_MOVZX__W, ALoad.getResult(P(p)), MO_AL(P(p), W_S, W))); 
}
  }

  /**
   * Emit code for rule number 404:
   * uload16: USHORT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code404(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), W_S, W));
  }

  /**
   * Emit code for rule number 407:
   * load32:	INT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code407(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), DW));
  }

  /**
   * Emit code for rule number 408:
   * load32:	INT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code408(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 413:
   * load64:	LONG_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code413(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), QW));
  }

  /**
   * Emit code for rule number 414:
   * load64:	LONG_ALOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code414(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 415:
   * load64:	LONG_ALOAD(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code415(AbstractBURS_TreeNode p) {
    RegisterOperand index = ALoad.getIndex(P(p)).asRegister(); 
if (index.getRegister().isInteger()) { 
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
pushMO(MO_AL(P(p), QW_S, QW)); 
} else { 
pushMO(MO_AL(P(p), QW_S, QW)); 
}
  }

  /**
   * Emit code for rule number 418:
   * r:	LONG_2INT(r)
   * @param p BURS node to apply the rule to
   */
  private void code418(AbstractBURS_TreeNode p) {
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
   * Emit code for rule number 419:
   * stm:	INT_STORE(LONG_2INT(r), OTHER_OPERAND(riv,riv))
   * @param p BURS node to apply the rule to
   */
  private void code419(AbstractBURS_TreeNode p) {
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
   * Emit code for rule number 420:
   * stm:	INT_ASTORE(LONG_2INT(r), OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code420(AbstractBURS_TreeNode p) {
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
   * Emit code for rule number 421:
   * r:	LONG_2INT(load64)
   * @param p BURS node to apply the rule to
   */
  private void code421(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), setSize(consumeMO(), 4)));
  }

  /**
   * Emit code for rule number 422:
   * load32:      LONG_2INT(load64)
   * @param p BURS node to apply the rule to
   */
  private void code422(AbstractBURS_TreeNode p) {
    pushMO(setSize(consumeMO(), 4));
  }

  /**
   * Emit code for rule number 423:
   * r:	LONG_2INT(LONG_USHR(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code423(AbstractBURS_TreeNode p) {
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
   * Emit code for rule number 424:
   * r:      LONG_2INT(LONG_SHR(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code424(AbstractBURS_TreeNode p) {
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
   * Emit code for rule number 425:
   * r:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code425(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), mo));
  }

  /**
   * Emit code for rule number 426:
   * r:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code426(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Unary.getResult(P(p)), mo));
  }

  /**
   * Emit code for rule number 427:
   * load32:      LONG_2INT(LONG_USHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code427(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
pushMO(mo);
  }

  /**
   * Emit code for rule number 428:
   * load32:      LONG_2INT(LONG_SHR(load64, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code428(AbstractBURS_TreeNode p) {
    MemoryOperand mo = consumeMO(); 
mo.disp = mo.disp.plus(4); 
mo = setSize(mo,4); 
pushMO(mo);
  }

  /**
   * Emit code for rule number 429:
   * czr:	LONG_ADD(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code429(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isLongConstant()) { 
  if (Bits.fits(Binary.getVal2(P(p)).asLongConstant().value, 32)) { 
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), IC(Binary.getVal2(P(p)).asLongConstant().lower32())); 
  } else { 
    RegisterOperand tmp = regpool.makeTempLong(); 
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, tmp, Binary.getClearVal2(P(p))))); 
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), tmp.copy()); 
  } 
} else { 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 430:
   * czr:	LONG_ADD(r, riv)
   * @param p BURS node to apply the rule to
   */
  private void code430(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 431:
   * czr:    LONG_ADD(r,r)
   * @param p BURS node to apply the rule to
   */
  private void code431(AbstractBURS_TreeNode p) {
    if (Binary.getVal1(P(p)).asRegister().getRegister().isInteger()) { 
RegisterOperand tmp = regpool.makeTempLong(); 
EMIT(CPOS(P(p), MIR_Unary.create(IA32_MOVSXDQ, tmp,Binary.getClearVal1(P(p))))); 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)),tmp.copy(), Binary.getClearVal2(P(p))); 
} else if (Binary.getVal2(P(p)).asRegister().getRegister().isInteger()) { 
RegisterOperand tmp = regpool.makeTempLong(); 
EMIT(CPOS(P(p), MIR_Unary.create(IA32_MOVSXDQ, tmp,Binary.getClearVal2(P(p))))); 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)),Binary.getClearVal1(P(p)),tmp.copy()); 
} else { 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 432:
   * r:	LONG_ADD(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code432(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isLongConstant()) { 
  pushAddress(R(Binary.getClearVal1(P(p))), null, B_S, Offset.fromLong(LV(Binary.getClearVal2(P(p))))); 
} else { 
  pushAddress(R(Binary.getClearVal1(P(p))), R(Binary.getClearVal2(P(p))), B_S, Offset.zero()); 
} 
EMIT_Lea(P(p), Binary.getClearResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 433:
   * czr:	LONG_ADD(rlv, load64)
   * @param p BURS node to apply the rule to
   */
  private void code433(AbstractBURS_TreeNode p) {
    if (Binary.getVal1(P(p)).isLongConstant()) { 
RegisterOperand tmp = regpool.makeTempLong(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, tmp,Binary.getClearVal1(P(p))))); 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), tmp.copy(), consumeMO()); 
} else { 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO()); 
}
  }

  /**
   * Emit code for rule number 434:
   * czr:	LONG_ADD(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code434(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isLongConstant()) { 
RegisterOperand tmp = regpool.makeTempLong(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, tmp, Binary.getClearVal2(P(p))))); 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), consumeMO(), tmp.copy()); 
} else { 
EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO()); 
}
  }

  /**
   * Emit code for rule number 435:
   * stm:	LONG_STORE(LONG_ADD(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code435(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 436:
   * stm:	LONG_STORE(LONG_ADD(rlv,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code436(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 437:
   * stm:	LONG_ASTORE(LONG_ADD(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code437(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 438:
   * stm:	LONG_ASTORE(LONG_ADD(rlv,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code438(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_ADD, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 439:
   * szpr:	LONG_AND(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code439(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isLongConstant()) { 
  if (Bits.fits(Binary.getVal2(P(p)).asLongConstant().value, 32)) { 
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), IC(Binary.getVal2(P(p)).asLongConstant().lower32()));   
  } else { 
    Register tmp = regpool.getLong(); 
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Long), Binary.getClearVal2(P(p))))); 
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(tmp, TypeReference.Long)); 
  } 
}else{
EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 440:
   * szpr:    LONG_AND(r,r)
   * @param p BURS node to apply the rule to
   */
  private void code440(AbstractBURS_TreeNode p) {
    if (Binary.getVal1(P(p)).asRegister().getRegister().isInteger()) { 
RegisterOperand tmp = regpool.makeTempLong(); 
EMIT(CPOS(P(p), MIR_Unary.create(IA32_MOVSXDQ, tmp, Binary.getClearVal1(P(p))))); 
EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), tmp, Binary.getClearVal2(P(p))); 
} else if (Binary.getVal2(P(p)).asRegister().getRegister().isInteger()) { 
RegisterOperand tmp = regpool.makeTempLong(); 
EMIT(CPOS(P(p), MIR_Unary.create(IA32_MOVSXDQ, tmp, Binary.getClearVal2(P(p))))); 
EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), tmp); 
} else { 
EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 441:
   * szp:	LONG_AND(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code441(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, Binary.getVal1(P(p)), Binary.getVal2(P(p))));
  }

  /**
   * Emit code for rule number 442:
   * szpr:	LONG_AND(rlv, load64)
   * @param p BURS node to apply the rule to
   */
  private void code442(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 443:
   * szpr:	LONG_AND(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code443(AbstractBURS_TreeNode p) {
    if (Binary.getVal2(P(p)).isLongConstant()) { 
  if (Bits.fits(Binary.getVal2(P(p)).asLongConstant().value, 32)) { 
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), IC(Binary.getVal2(P(p)).asLongConstant().lower32()), consumeMO());   
  } else { 
    Register tmp = regpool.getLong(); 
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Long), Binary.getClearVal2(P(p))))); 
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), new RegisterOperand(tmp, TypeReference.Long), consumeMO()); 
  } 
} else { 
EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO()); 
}
  }

  /**
   * Emit code for rule number 444:
   * szp:	LONG_AND(load8_16_32_64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code444(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, consumeMO(), Binary.getVal2(P(p))));
  }

  /**
   * Emit code for rule number 445:
   * szp:	LONG_AND(r, load8_16_32_64)
   * @param p BURS node to apply the rule to
   */
  private void code445(AbstractBURS_TreeNode p) {
    EMIT(MIR_Test.mutate(P(p), IA32_TEST, consumeMO(), Binary.getVal1(P(p))));
  }

  /**
   * Emit code for rule number 446:
   * stm:	LONG_STORE(LONG_AND(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code446(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 447:
   * stm:	LONG_STORE(LONG_AND(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code447(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 448:
   * stm:	LONG_ASTORE(LONG_AND(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code448(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p)));
  }

  /**
   * Emit code for rule number 449:
   * stm:	LONG_ASTORE(LONG_AND(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code449(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal1(PL(p)));
  }

  /**
   * Emit code for rule number 450:
   * r:  LONG_DIV(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code450(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), true, true);
  }

  /**
   * Emit code for rule number 451:
   * r:  LONG_DIV(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code451(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), true, true);
  }

  /**
   * Emit code for rule number 452:
   * r:  LONG_DIV(riv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code452(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), true, true);
  }

  /**
   * Emit code for rule number 453:
   * r:  LONG_DIV(rlv, load64)
   * @param p BURS node to apply the rule to
   */
  private void code453(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            consumeMO(), true, true);
  }

  /**
   * Emit code for rule number 454:
   * r:  LONG_DIV(load64,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code454(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), consumeMO(), GuardedBinary.getClearVal2(P(p)), 
           true, true);
  }

  /**
   * Emit code for rule number 455:
   * stm:	LONG_IFCMP(rlv,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code455(AbstractBURS_TreeNode p) {
    if (IfCmp.getVal1(P(p)).isLongConstant()) { 
Register tmp = regpool.getLong(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Long),IfCmp.getClearVal1(P(p))))); 
IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), new RegisterOperand(tmp, TypeReference.Long), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p))); 
} else if (IfCmp.getVal2(P(p)).isLongConstant()) { 
Register tmp = regpool.getLong(); 
EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(tmp, TypeReference.Long), IfCmp.getClearVal2(P(p))))); 
IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), new RegisterOperand(tmp, TypeReference.Long), IfCmp.getCond(P(p))); 
} else { 
IFCMP(P(p), IfCmp.getClearGuardResult(P(p)), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)), IfCmp.getCond(P(p))); 
}
  }

  /**
   * Emit code for rule number 456:
   * stm:	LONG_IFCMP(r, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code456(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), Move.create(GUARD_MOVE, IfCmp.getClearGuardResult(P(p)), new TrueGuardOperand()))); 
EMIT(CPOS(P(p), MIR_Test.create(IA32_TEST, IfCmp.getVal1(P(p)).copy(), IfCmp.getClearVal1(P(p))))); 
EMIT(MIR_CondBranch.mutate(P(p), IA32_JCC, COND(IfCmp.getCond(P(p))), IfCmp.getClearTarget(P(p)), IfCmp.getClearBranchProfile(P(p))));
  }

  /**
   * Emit code for rule number 457:
   * r:	LONG_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code457(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 458:
   * r:	LONG_LOAD(rlv, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code458(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getAddress(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
		     consumeAddress(QW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 459:
   * r:	LONG_LOAD(address1scaledreg, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code459(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(QW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 460:
   * r:	LONG_LOAD(address1scaledreg, address1reg)
   * @param p BURS node to apply the rule to
   */
  private void code460(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(QW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 461:
   * r:	LONG_LOAD(address1reg, address1scaledreg)
   * @param p BURS node to apply the rule to
   */
  private void code461(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(QW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 462:
   * r:	LONG_LOAD(address, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code462(AbstractBURS_TreeNode p) {
    augmentAddress(Load.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, Load.getResult(P(p)), 
	             consumeAddress(QW, Load.getLocation(P(p)), Load.getGuard(P(p)))));
  }

  /**
   * Emit code for rule number 463:
   * r:      LONG_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code463(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 464:
   * r:      LONG_ALOAD(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code464(AbstractBURS_TreeNode p) {
    RegisterOperand index = ALoad.getIndex(P(p)).asRegister(); 
if (index.getRegister().isInteger()) { 
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW))); 
} else { 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW))); 
}
  }

  /**
   * Emit code for rule number 465:
   * r:	LONG_MOVE(rlv)
   * @param p BURS node to apply the rule to
   */
  private void code465(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 466:
   * r:  LONG_MOVE(riv)
   * @param p BURS node to apply the rule to
   */
  private void code466(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 468:
   * r:	LONG_MUL(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code468(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 469:
   * r:	INT_MUL(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code469(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 470:
   * r:	INT_MUL(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code470(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_IMUL2, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 471:
   * szpr:	LONG_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code471(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 472:
   * stm:	LONG_STORE(LONG_NEG(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code472(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), MO_S(P(p), QW), MO_S(P(p), QW));
  }

  /**
   * Emit code for rule number 473:
   * stm:	LONG_ASTORE(LONG_NEG(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code473(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NEG, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 474:
   * r:	LONG_NOT(r)
   * @param p BURS node to apply the rule to
   */
  private void code474(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 475:
   * stm:	LONG_STORE(LONG_NOT(LONG_LOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code475(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), MO_S(P(p), QW), MO_S(P(p), QW));
  }

  /**
   * Emit code for rule number 476:
   * stm:	LONG_ASTORE(LONG_NOT(LONG_ALOAD(riv,riv)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code476(AbstractBURS_TreeNode p) {
    EMIT_Unary(IA32_NOT, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 477:
   * szpr:	LONG_OR(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code477(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 478:
   * szpr:	LONG_OR(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code478(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 479:
   * szpr:	LONG_OR(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code479(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 480:
   * stm:	LONG_STORE(LONG_OR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code480(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal2(PL(p)) );
  }

  /**
   * Emit code for rule number 481:
   * stm:	LONG_STORE(LONG_OR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code481(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal1(PL(p)) );
  }

  /**
   * Emit code for rule number 482:
   * stm:	LONG_ASTORE(LONG_OR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code482(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p)) );
  }

  /**
   * Emit code for rule number 483:
   * stm:	LONG_ASTORE(LONG_OR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code483(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_OR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal1(PL(p)) );
  }

  /**
   * Emit code for rule number 484:
   * r:  LONG_REM(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code484(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), false, true);
  }

  /**
   * Emit code for rule number 485:
   * r:  LONG_REM(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code485(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), false, true);
  }

  /**
   * Emit code for rule number 486:
   * r:  LONG_REM(riv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code486(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            GuardedBinary.getClearVal2(P(p)), false, true);
  }

  /**
   * Emit code for rule number 487:
   * r:  LONG_REM(rlv, load64)
   * @param p BURS node to apply the rule to
   */
  private void code487(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), GuardedBinary.getClearVal1(P(p)), 
            consumeMO(), false, true);
  }

  /**
   * Emit code for rule number 488:
   * r:  LONG_REM(load64,rlv)
   * @param p BURS node to apply the rule to
   */
  private void code488(AbstractBURS_TreeNode p) {
    LONG_DIVIDES(P(p), GuardedBinary.getClearResult(P(p)), consumeMO(), GuardedBinary.getClearVal2(P(p)), 
           false, true);
  }

  /**
   * Emit code for rule number 489:
   * szpr:	LONG_SHL(rlv, INT_AND(r, INT_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code489(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 490:
   * szpr:	LONG_SHL(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code490(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 491:
   * szpr:	LONG_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code491(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 63); if(Binary.getVal2(P(p)).asIntConstant().value == 1) { 
 EMIT_Commutative(IA32_ADD, P(p), Binary.getClearResult(P(p)), Binary.getVal1(P(p)).copy(), Binary.getClearVal1(P(p))); 
} else { 
 EMIT_NonCommutative(IA32_SHL, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p))); 
}
  }

  /**
   * Emit code for rule number 492:
   * r:	LONG_SHL(r, INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code492(AbstractBURS_TreeNode p) {
    pushAddress(null, Binary.getClearVal1(P(p)).asRegister(), LEA_SHIFT(Binary.getClearVal2(P(p))), Offset.zero()); 
EMIT_Lea(P(p), Binary.getClearResult(P(p)), consumeAddress(QW, null, null));
  }

  /**
   * Emit code for rule number 493:
   * szpr:	LONG_SHL(LONG_SHR(r, INT_CONSTANT), INT_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code493(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_AND, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(PL(p)), IC(0xffffffff << VR(p)));
  }

  /**
   * Emit code for rule number 494:
   * stm:	LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv),INT_AND(r,INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code494(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_S(P(p), QW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 495:
   * stm:	LONG_STORE(LONG_SHL(LONG_LOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code495(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 63); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_S(P(p), QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 496:
   * stm:	LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv),INT_AND(r, INT_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code496(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_AS(P(p), QW_S, QW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 497:
   * stm:	LONG_ASTORE(LONG_SHL(LONG_ALOAD(riv,riv), INT_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code497(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHL, MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 498:
   * szpr:	LONG_SHR(rlv, INT_AND(r, LONG_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code498(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 499:
   * szpr:	LONG_SHR(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code499(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 500:
   * szpr:	LONG_SHR(rlv, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code500(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 63); 
EMIT_NonCommutative(IA32_SAR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 501:
   * stm:	LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv),INT_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code501(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_S(P(p), QW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 502:
   * stm:	LONG_STORE(LONG_SHR(LONG_LOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code502(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 63); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_S(P(p), QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 503:
   * stm:	LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv),INT_AND(r, LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code503(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_AS(P(p), QW_S, QW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 504:
   * stm:	LONG_ASTORE(LONG_SHR(LONG_ALOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code504(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SAR, MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 505:
   * stm:	LONG_STORE(rlv, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code505(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOV, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 506:
   * stm:	LONG_STORE(rlv, OTHER_OPERAND(rlv, address1scaledreg))
   * @param p BURS node to apply the rule to
   */
  private void code506(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getAddress(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, 
                     consumeAddress(QW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 507:
   * stm:	LONG_STORE(rlv, OTHER_OPERAND(address1scaledreg, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code507(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV, 
                     consumeAddress(QW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 508:
   * stm:	LONG_STORE(rlv, OTHER_OPERAND(address1scaledreg, address1reg))
   * @param p BURS node to apply the rule to
   */
  private void code508(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
                    consumeAddress(QW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
                    Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 509:
   * stm:	LONG_STORE(rlv, OTHER_OPERAND(address1reg, address1scaledreg))
   * @param p BURS node to apply the rule to
   */
  private void code509(AbstractBURS_TreeNode p) {
    combineAddresses(); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
                    consumeAddress(QW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
                    Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 510:
   * stm:	LONG_STORE(rlv, OTHER_OPERAND(address, LONG_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code510(AbstractBURS_TreeNode p) {
    augmentAddress(Store.getOffset(P(p))); 
EMIT(MIR_Move.mutate(P(p), IA32_MOV,  
	             consumeAddress(QW, Store.getLocation(P(p)), Store.getGuard(P(p))), 
		     Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 511:
   * czr:	LONG_SUB(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code511(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 512:
   * r:	LONG_SUB(rlv, r)
   * @param p BURS node to apply the rule to
   */
  private void code512(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, Binary.getResult(P(p)).copy()))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, Binary.getClearResult(P(p)), Binary.getClearVal1(P(p))));
  }

  /**
   * Emit code for rule number 513:
   * r:	LONG_SUB(load64, r)
   * @param p BURS node to apply the rule to
   */
  private void code513(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, Binary.getResult(P(p)).copy()))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, Binary.getClearResult(P(p)), consumeMO()));
  }

  /**
   * Emit code for rule number 514:
   * czr:	LONG_SUB(rlv, load64)
   * @param p BURS node to apply the rule to
   */
  private void code514(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 515:
   * czr:	LONG_SUB(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code515(AbstractBURS_TreeNode p) {
    EMIT_NonCommutative(IA32_SUB, P(p), Binary.getClearResult(P(p)), consumeMO(), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 516:
   * stm:	LONG_STORE(LONG_SUB(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code516(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SUB, MO_S(P(p), QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 517:
   * stm:	LONG_STORE(LONG_SUB(rlv, LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code517(AbstractBURS_TreeNode p) {
    MemoryOperand result = MO_S(P(p), QW); 
EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, result))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, result.copy(), Binary.getClearVal1(PL(p))));
  }

  /**
   * Emit code for rule number 518:
   * stm:	LONG_ASTORE(LONG_SUB(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code518(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SUB, MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 519:
   * stm:	LONG_ASTORE(LONG_SUB(rlv, LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code519(AbstractBURS_TreeNode p) {
    MemoryOperand result = MO_AS(P(p), QW_S, QW); 
EMIT(CPOS(P(p), MIR_UnaryAcc.create(IA32_NEG, result))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_ADD, result.copy(), Binary.getClearVal1(PL(p))));
  }

  /**
   * Emit code for rule number 520:
   * szpr:	LONG_USHR(rlv, LONG_AND(r, LONG_CONSTANT))
   * @param p BURS node to apply the rule to
   */
  private void code520(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PR(p))))); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 521:
   * szpr:	LONG_USHR(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code521(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal2(P(p))))); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), new RegisterOperand(getECX(), TypeReference.Int));
  }

  /**
   * Emit code for rule number 522:
   * szpr:	LONG_USHR(rlv, LONG_CONSTANT)
   * @param p BURS node to apply the rule to
   */
  private void code522(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VR(p) & 0x7FFFFFFF) <= 63); 
EMIT_NonCommutative(IA32_SHR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 523:
   * stm:	LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv),LONG_AND(r,LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code523(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p))))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_S(P(p), QW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 524:
   * stm:	LONG_STORE(LONG_USHR(LONG_LOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code524(AbstractBURS_TreeNode p) {
    if (VM.VerifyAssertions) VM._assert((VLR(p) & 0x7FFFFFFF) <= 63); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_S(P(p), QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 525:
   * stm:	LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv),LONG_AND(r, LONG_CONSTANT)),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code525(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.create(IA32_MOV, new RegisterOperand(getECX(), TypeReference.Int), Binary.getClearVal1(PLR(p)))); 
EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_AS(P(p), QW_S, QW), new RegisterOperand(getECX(), TypeReference.Int)));
  }

  /**
   * Emit code for rule number 526:
   * stm:	LONG_ASTORE(LONG_USHR(LONG_ALOAD(riv,riv), LONG_CONSTANT),OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code526(AbstractBURS_TreeNode p) {
    EMIT(MIR_BinaryAcc.mutate(P(p), IA32_SHR, MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p))));
  }

  /**
   * Emit code for rule number 527:
   * szpr:	LONG_XOR(r, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code527(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 528:
   * szpr:	LONG_XOR(r, load64)
   * @param p BURS node to apply the rule to
   */
  private void code528(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 529:
   * szpr:	LONG_XOR(load64, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code529(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 530:
   * stm:	LONG_STORE(LONG_XOR(LONG_LOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code530(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal2(PL(p)) );
  }

  /**
   * Emit code for rule number 531:
   * stm:	LONG_STORE(LONG_XOR(r,LONG_LOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code531(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_S(P(p), QW), MO_S(P(p), QW), Binary.getClearVal1(PL(p)) );
  }

  /**
   * Emit code for rule number 532:
   * stm:	LONG_ASTORE(LONG_XOR(LONG_ALOAD(rlv,rlv),rlv),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code532(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal2(PL(p)) );
  }

  /**
   * Emit code for rule number 533:
   * stm:	LONG_ASTORE(LONG_XOR(r,LONG_ALOAD(rlv,rlv)),OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code533(AbstractBURS_TreeNode p) {
    EMIT_Commutative(IA32_XOR, P(p), MO_AS(P(p), QW_S, QW), MO_AS(P(p), QW_S, QW), Binary.getClearVal1(PL(p)) );
  }

  /**
   * Emit code for rule number 534:
   * r: FLOAT_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code534(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 535:
   * r: FLOAT_ADD(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code535(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 536:
   * r: FLOAT_ADD(float_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code536(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 537:
   * r: DOUBLE_ADD(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code537(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), Binary.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 538:
   * r: DOUBLE_ADD(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code538(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 539:
   * r: DOUBLE_ADD(double_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code539(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_ADDSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 540:
   * r: FLOAT_SUB(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code540(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 541:
   * r: FLOAT_SUB(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code541(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 542:
   * r: DOUBLE_SUB(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code542(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 543:
   * r: DOUBLE_SUB(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code543(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_SUBSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 544:
   * r: FLOAT_MUL(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code544(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 545:
   * r: FLOAT_MUL(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code545(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 546:
   * r: FLOAT_MUL(float_load, r)
   * @param p BURS node to apply the rule to
   */
  private void code546(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 547:
   * r: DOUBLE_MUL(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code547(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 548:
   * r: DOUBLE_MUL(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code548(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 549:
   * r: DOUBLE_MUL(double_load, r)
   * @param p BURS node to apply the rule to
   */
  private void code549(AbstractBURS_TreeNode p) {
    SSE2_COP(IA32_MULSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 550:
   * r: FLOAT_DIV(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code550(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 551:
   * r: FLOAT_DIV(r, float_load)
   * @param p BURS node to apply the rule to
   */
  private void code551(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSS, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 552:
   * r: DOUBLE_DIV(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code552(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), Binary.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 553:
   * r: DOUBLE_DIV(r, double_load)
   * @param p BURS node to apply the rule to
   */
  private void code553(AbstractBURS_TreeNode p) {
    SSE2_NCOP(IA32_DIVSD, P(p), Binary.getClearResult(P(p)), Binary.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 554:
   * r: FLOAT_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code554(AbstractBURS_TreeNode p) {
    SSE2_NEG(true, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 555:
   * r: DOUBLE_NEG(r)
   * @param p BURS node to apply the rule to
   */
  private void code555(AbstractBURS_TreeNode p) {
    SSE2_NEG(false, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 556:
   * r: FLOAT_SQRT(r)
   * @param p BURS node to apply the rule to
   */
  private void code556(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_SQRTSS, Unary.getClearResult(P(p)), Unary.getClearVal(P(p))));
  }

  /**
   * Emit code for rule number 557:
   * r: DOUBLE_SQRT(r)
   * @param p BURS node to apply the rule to
   */
  private void code557(AbstractBURS_TreeNode p) {
    EMIT(MIR_Unary.mutate(P(p), IA32_SQRTSD, Unary.getClearResult(P(p)), Unary.getClearVal(P(p))));
  }

  /**
   * Emit code for rule number 558:
   * r: FLOAT_REM(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code558(AbstractBURS_TreeNode p) {
    SSE2_X87_REM(P(p));
  }

  /**
   * Emit code for rule number 559:
   * r: DOUBLE_REM(r, r)
   * @param p BURS node to apply the rule to
   */
  private void code559(AbstractBURS_TreeNode p) {
    SSE2_X87_REM(P(p));
  }

  /**
   * Emit code for rule number 560:
   * r: LONG_2FLOAT(r)
   * @param p BURS node to apply the rule to
   */
  private void code560(AbstractBURS_TreeNode p) {
    SSE2_X87_FROMLONG(P(p));
  }

  /**
   * Emit code for rule number 561:
   * r: LONG_2DOUBLE(r)
   * @param p BURS node to apply the rule to
   */
  private void code561(AbstractBURS_TreeNode p) {
    SSE2_X87_FROMLONG(P(p));
  }

  /**
   * Emit code for rule number 562:
   * r: FLOAT_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code562(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVAPS, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 563:
   * r: DOUBLE_MOVE(r)
   * @param p BURS node to apply the rule to
   */
  private void code563(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVAPD, Move.getResult(P(p)), Move.getVal(P(p))));
  }

  /**
   * Emit code for rule number 564:
   * r: DOUBLE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code564(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 565:
   * r: DOUBLE_LOAD(riv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code565(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 566:
   * r: DOUBLE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code566(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, Load.getResult(P(p)), MO_L(P(p), QW)));
  }

  /**
   * Emit code for rule number 567:
   * double_load: DOUBLE_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code567(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), QW));
  }

  /**
   * Emit code for rule number 568:
   * r: DOUBLE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code568(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 569:
   * r: DOUBLE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code569(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 570:
   * double_load: DOUBLE_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code570(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), QW));
  }

  /**
   * Emit code for rule number 571:
   * r: DOUBLE_ALOAD(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code571(AbstractBURS_TreeNode p) {
    RegisterOperand index=ALoad.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
}
  }

  /**
   * Emit code for rule number 572:
   * r: DOUBLE_ALOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code572(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, ALoad.getResult(P(p)), MO_AL(P(p), QW_S, QW)));
  }

  /**
   * Emit code for rule number 573:
   * double_load: DOUBLE_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code573(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 574:
   * double_load: DOUBLE_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code574(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), QW_S, QW));
  }

  /**
   * Emit code for rule number 575:
   * r: FLOAT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code575(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, Load.getResult(P(p)), MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 576:
   * r: FLOAT_LOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code576(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, Load.getResult(P(p)), MO_L(P(p), DW)));
  }

  /**
   * Emit code for rule number 577:
   * float_load: FLOAT_LOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code577(AbstractBURS_TreeNode p) {
    pushMO(MO_L(P(p), DW));
  }

  /**
   * Emit code for rule number 578:
   * float_load: FLOAT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code578(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 579:
   * r: FLOAT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code579(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 580:
   * r: FLOAT_ALOAD(rlv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code580(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 581:
   * r: FLOAT_ALOAD(riv, r)
   * @param p BURS node to apply the rule to
   */
  private void code581(AbstractBURS_TreeNode p) {
    RegisterOperand index=ALoad.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
}
  }

  /**
   * Emit code for rule number 582:
   * r: FLOAT_ALOAD(rlv, rlv)
   * @param p BURS node to apply the rule to
   */
  private void code582(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, ALoad.getResult(P(p)), MO_AL(P(p), DW_S, DW)));
  }

  /**
   * Emit code for rule number 583:
   * float_load: FLOAT_ALOAD(riv, riv)
   * @param p BURS node to apply the rule to
   */
  private void code583(AbstractBURS_TreeNode p) {
    pushMO(MO_AL(P(p), DW_S, DW));
  }

  /**
   * Emit code for rule number 584:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code584(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 585:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code585(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 586:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code586(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 587:
   * stm: DOUBLE_STORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code587(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_S(P(p), QW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 588:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code588(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 589:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code589(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 590:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code590(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 591:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code591(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 592:
   * stm: DOUBLE_ASTORE(r, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code592(AbstractBURS_TreeNode p) {
    RegisterOperand index=AStore.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSD, MO_AS(P(p), QW_S, QW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 593:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code593(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 594:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code594(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 595:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code595(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 596:
   * stm: FLOAT_STORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code596(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_S(P(p), DW), Store.getValue(P(p))));
  }

  /**
   * Emit code for rule number 597:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code597(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 598:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code598(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 599:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(riv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code599(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 600:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(rlv, rlv))
   * @param p BURS node to apply the rule to
   */
  private void code600(AbstractBURS_TreeNode p) {
    EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
  }

  /**
   * Emit code for rule number 601:
   * stm: FLOAT_ASTORE(r, OTHER_OPERAND(r, r))
   * @param p BURS node to apply the rule to
   */
  private void code601(AbstractBURS_TreeNode p) {
    RegisterOperand index=AStore.getIndex(P(p)).asRegister();
if (VM.BuildFor64Addr && index.getRegister().isInteger()){
CLEAR_UPPER_32(P(p), index.copy().asRegister()); 
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
}else{
EMIT(MIR_Move.mutate(P(p), IA32_MOVSS, MO_AS(P(p), DW_S, DW), AStore.getValue(P(p))));
}
  }

  /**
   * Emit code for rule number 602:
   * r: INT_2FLOAT(riv)
   * @param p BURS node to apply the rule to
   */
  private void code602(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SS, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 603:
   * r: INT_2FLOAT(load32)
   * @param p BURS node to apply the rule to
   */
  private void code603(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SS, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 604:
   * r: INT_2DOUBLE(riv)
   * @param p BURS node to apply the rule to
   */
  private void code604(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SD, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 605:
   * r: INT_2DOUBLE(load32)
   * @param p BURS node to apply the rule to
   */
  private void code605(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSI2SD, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 606:
   * r: FLOAT_2DOUBLE(r)
   * @param p BURS node to apply the rule to
   */
  private void code606(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSS2SD, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 607:
   * r: FLOAT_2DOUBLE(float_load)
   * @param p BURS node to apply the rule to
   */
  private void code607(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSS2SD, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 608:
   * r: DOUBLE_2FLOAT(r)
   * @param p BURS node to apply the rule to
   */
  private void code608(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSD2SS, P(p), Unary.getClearResult(P(p)), Unary.getClearVal(P(p)));
  }

  /**
   * Emit code for rule number 609:
   * r: DOUBLE_2FLOAT(double_load)
   * @param p BURS node to apply the rule to
   */
  private void code609(AbstractBURS_TreeNode p) {
    SSE2_CONV(IA32_CVTSD2SS, P(p), Unary.getClearResult(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 610:
   * r: FLOAT_2INT(r)
   * @param p BURS node to apply the rule to
   */
  private void code610(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 611:
   * r: FLOAT_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code611(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 612:
   * r: DOUBLE_2INT(r)
   * @param p BURS node to apply the rule to
   */
  private void code612(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 613:
   * r: DOUBLE_2LONG(r)
   * @param p BURS node to apply the rule to
   */
  private void code613(AbstractBURS_TreeNode p) {
    EMIT(P(p)); /* leave for complex operators */
  }

  /**
   * Emit code for rule number 614:
   * r: FLOAT_AS_INT_BITS(r)
   * @param p BURS node to apply the rule to
   */
  private void code614(AbstractBURS_TreeNode p) {
    SSE2_FPR2GPR_32(P(p));
  }

  /**
   * Emit code for rule number 616:
   * r: DOUBLE_AS_LONG_BITS(r)
   * @param p BURS node to apply the rule to
   */
  private void code616(AbstractBURS_TreeNode p) {
    SSE2_FPR2GPR_64(P(p));
  }

  /**
   * Emit code for rule number 618:
   * r: INT_BITS_AS_FLOAT(riv)
   * @param p BURS node to apply the rule to
   */
  private void code618(AbstractBURS_TreeNode p) {
    SSE2_GPR2FPR_32(P(p));
  }

  /**
   * Emit code for rule number 620:
   * r: LONG_BITS_AS_DOUBLE(rlv)
   * @param p BURS node to apply the rule to
   */
  private void code620(AbstractBURS_TreeNode p) {
    SSE2_GPR2FPR_64(P(p));
  }

  /**
   * Emit code for rule number 622:
   * r: MATERIALIZE_FP_CONSTANT(any)
   * @param p BURS node to apply the rule to
   */
  private void code622(AbstractBURS_TreeNode p) {
    SSE2_FPCONSTANT(P(p));
  }

  /**
   * Emit code for rule number 623:
   * float_load: MATERIALIZE_FP_CONSTANT(any)
   * @param p BURS node to apply the rule to
   */
  private void code623(AbstractBURS_TreeNode p) {
    pushMO(MO_MC(P(p)));
  }

  /**
   * Emit code for rule number 624:
   * double_load: MATERIALIZE_FP_CONSTANT(any)
   * @param p BURS node to apply the rule to
   */
  private void code624(AbstractBURS_TreeNode p) {
    pushMO(MO_MC(P(p)));
  }

  /**
   * Emit code for rule number 625:
   * stm: CLEAR_FLOATING_POINT_STATE
   * @param p BURS node to apply the rule to
   */
  private void code625(AbstractBURS_TreeNode p) {
    EMIT(MIR_Empty.mutate(P(p), IA32_FNINIT));
  }

  /**
   * Emit code for rule number 626:
   * stm: FLOAT_IFCMP(r,r)
   * @param p BURS node to apply the rule to
   */
  private void code626(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISS, P(p), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 627:
   * stm: FLOAT_IFCMP(r,float_load)
   * @param p BURS node to apply the rule to
   */
  private void code627(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISS, P(p), IfCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 628:
   * stm: FLOAT_IFCMP(float_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code628(AbstractBURS_TreeNode p) {
    IfCmp.getCond(P(p)).flipOperands(); SSE2_IFCMP(IA32_UCOMISS, P(p), IfCmp.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 629:
   * stm: DOUBLE_IFCMP(r,r)
   * @param p BURS node to apply the rule to
   */
  private void code629(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISD, P(p), IfCmp.getClearVal1(P(p)), IfCmp.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 630:
   * stm: DOUBLE_IFCMP(r,double_load)
   * @param p BURS node to apply the rule to
   */
  private void code630(AbstractBURS_TreeNode p) {
    SSE2_IFCMP(IA32_UCOMISD, P(p), IfCmp.getClearVal1(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 631:
   * stm: DOUBLE_IFCMP(double_load,r)
   * @param p BURS node to apply the rule to
   */
  private void code631(AbstractBURS_TreeNode p) {
    IfCmp.getCond(P(p)).flipOperands(); SSE2_IFCMP(IA32_UCOMISD, P(p), IfCmp.getClearVal2(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 632:
   * r: FCMP_CMOV(r, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code632(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(CondMove.getVal1(P(p)).isFloat() ? IA32_UCOMISS : IA32_UCOMISD,      CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p))))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 633:
   * r: FCMP_CMOV(r, OTHER_OPERAND(float_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code633(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISS, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 634:
   * r: FCMP_CMOV(r, OTHER_OPERAND(double_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code634(AbstractBURS_TreeNode p) {
    EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISD, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 635:
   * r: FCMP_CMOV(float_load, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code635(AbstractBURS_TreeNode p) {
    CondMove.getCond(P(p)).flipOperands(); EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISS, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 636:
   * r: FCMP_CMOV(double_load, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code636(AbstractBURS_TreeNode p) {
    CondMove.getCond(P(p)).flipOperands(); EMIT(CPOS(P(p), MIR_Compare.create(IA32_UCOMISD, CondMove.getClearVal1(P(p)), consumeMO()))); CMOV_MOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearCond(P(p)).translateUNSIGNED(),          CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 637:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, any))
   * @param p BURS node to apply the rule to
   */
  private void code637(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), CondMove.getClearTrueValue(P(p)), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 638:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, float_load)))
   * @param p BURS node to apply the rule to
   */
  private void code638(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), CondMove.getClearTrueValue(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 639:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(r, double_load)))
   * @param p BURS node to apply the rule to
   */
  private void code639(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), CondMove.getClearTrueValue(P(p)), consumeMO());
  }

  /**
   * Emit code for rule number 640:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(float_load, r)))
   * @param p BURS node to apply the rule to
   */
  private void code640(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), consumeMO(), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 641:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(r, OTHER_OPERAND(double_load, r)))
   * @param p BURS node to apply the rule to
   */
  private void code641(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), CondMove.getClearVal2(P(p)),                 CondMove.getClearCond(P(p)), consumeMO(), CondMove.getClearFalseValue(P(p)));
  }

  /**
   * Emit code for rule number 642:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(float_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code642(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), consumeMO(),                 CondMove.getClearCond(P(p)), CondMove.getClearFalseValue(P(p)), CondMove.getClearTrueValue(P(p)));
  }

  /**
   * Emit code for rule number 643:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(double_load, any))
   * @param p BURS node to apply the rule to
   */
  private void code643(AbstractBURS_TreeNode p) {
    SSE2_FCMP_FCMOV(P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)), consumeMO(),                 CondMove.getClearCond(P(p)), CondMove.getClearFalseValue(P(p)), CondMove.getClearTrueValue(P(p)));
  }

  /**
   * Emit code for rule number 644:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code644(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 645:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code645(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 646:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code646(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 647:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code647(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 648:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code648(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 649:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(FLOAT_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code649(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 650:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code650(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 651:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, FLOAT_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code651(AbstractBURS_TreeNode p) {
    SSE2_ABS(true, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 652:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code652(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 653:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code653(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 654:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code654(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 655:
   * r: FCMP_FCMOV(r, OTHER_OPERAND(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code655(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal1(P(p)));
  }

  /**
   * Emit code for rule number 656:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code656(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 657:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(DOUBLE_NEG(r), r)))
   * @param p BURS node to apply the rule to
   */
  private void code657(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 658:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(INT_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code658(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 659:
   * r: FCMP_FCMOV(MATERIALIZE_FP_CONSTANT(LONG_CONSTANT), OTHER_OPERAND(r, OTHER_OPERAND(r, DOUBLE_NEG(r))))
   * @param p BURS node to apply the rule to
   */
  private void code659(AbstractBURS_TreeNode p) {
    SSE2_ABS(false, P(p), CondMove.getClearResult(P(p)), CondMove.getClearVal2(P(p)));
  }

  /**
   * Emit code for rule number 660:
   * stm: LONG_ASTORE(load64, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code660(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_AS(P(p), QW_S, QW), temp.copyRO()));
  }

  /**
   * Emit code for rule number 661:
   * stm: LONG_ASTORE(load64, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code661(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_AS(P(p), QW_S, QW), temp.copyRO()));
  }

  /**
   * Emit code for rule number 662:
   * stm: LONG_STORE(load64, OTHER_OPERAND(riv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code662(AbstractBURS_TreeNode p) {
    RegisterOperand temp = regpool.makeTemp(TypeReference.Double); EMIT(MIR_Move.mutate(PL(p), IA32_MOVQ, temp, consumeMO())); EMIT(MIR_Move.mutate(P(p), IA32_MOVQ, MO_S(P(p), QW), temp.copyRO()));
  }

  /**
   * Emit code for rule number 663:
   * stm: LONG_STORE(load64, OTHER_OPERAND(rlv, riv))
   * @param p BURS node to apply the rule to
   */
  private void code663(AbstractBURS_TreeNode p) {
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
    case 95: code95(p); break;
    case 96: code96(p); break;
    case 97: code97(p); break;
    case 98: code98(p); break;
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
    case 152: code152(p); break;
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
    case 254: code254(p); break;
    case 255: code255(p); break;
    case 256: code256(p); break;
    case 257: code257(p); break;
    case 258: code258(p); break;
    case 259: code259(p); break;
    case 260: code260(p); break;
    case 261: code261(p); break;
    case 262: code262(p); break;
    case 263: code263(p); break;
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
    case 291: code291(p); break;
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
    case 352: code352(p); break;
    case 353: code353(p); break;
    case 354: code354(p); break;
    case 355: code355(p); break;
    case 356: code356(p); break;
    case 357: code357(p); break;
    case 358: code358(p); break;
    case 359: code359(p); break;
    case 360: code360(p); break;
    case 361: code361(p); break;
    case 362: code362(p); break;
    case 363: code363(p); break;
    case 364: code364(p); break;
    case 365: code365(p); break;
    case 366: code366(p); break;
    case 367: code367(p); break;
    case 368: code368(p); break;
    case 369: code369(p); break;
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
    case 395: code395(p); break;
    case 396: code396(p); break;
    case 397: code397(p); break;
    case 398: code398(p); break;
    case 399: code399(p); break;
    case 400: code400(p); break;
    case 401: code401(p); break;
    case 402: code402(p); break;
    case 403: code403(p); break;
    case 404: code404(p); break;
    case 407: code407(p); break;
    case 408: code408(p); break;
    case 413: code413(p); break;
    case 414: code414(p); break;
    case 415: code415(p); break;
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
    case 521: code521(p); break;
    case 522: code522(p); break;
    case 523: code523(p); break;
    case 524: code524(p); break;
    case 525: code525(p); break;
    case 526: code526(p); break;
    case 527: code527(p); break;
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
    case 570: code570(p); break;
    case 571: code571(p); break;
    case 572: code572(p); break;
    case 573: code573(p); break;
    case 574: code574(p); break;
    case 575: code575(p); break;
    case 576: code576(p); break;
    case 577: code577(p); break;
    case 578: code578(p); break;
    case 579: code579(p); break;
    case 580: code580(p); break;
    case 581: code581(p); break;
    case 582: code582(p); break;
    case 583: code583(p); break;
    case 584: code584(p); break;
    case 585: code585(p); break;
    case 586: code586(p); break;
    case 587: code587(p); break;
    case 588: code588(p); break;
    case 589: code589(p); break;
    case 590: code590(p); break;
    case 591: code591(p); break;
    case 592: code592(p); break;
    case 593: code593(p); break;
    case 594: code594(p); break;
    case 595: code595(p); break;
    case 596: code596(p); break;
    case 597: code597(p); break;
    case 598: code598(p); break;
    case 599: code599(p); break;
    case 600: code600(p); break;
    case 601: code601(p); break;
    case 602: code602(p); break;
    case 603: code603(p); break;
    case 604: code604(p); break;
    case 605: code605(p); break;
    case 606: code606(p); break;
    case 607: code607(p); break;
    case 608: code608(p); break;
    case 609: code609(p); break;
    case 610: code610(p); break;
    case 611: code611(p); break;
    case 612: code612(p); break;
    case 613: code613(p); break;
    case 614: code614(p); break;
    case 616: code616(p); break;
    case 618: code618(p); break;
    case 620: code620(p); break;
    case 622: code622(p); break;
    case 623: code623(p); break;
    case 624: code624(p); break;
    case 625: code625(p); break;
    case 626: code626(p); break;
    case 627: code627(p); break;
    case 628: code628(p); break;
    case 629: code629(p); break;
    case 630: code630(p); break;
    case 631: code631(p); break;
    case 632: code632(p); break;
    case 633: code633(p); break;
    case 634: code634(p); break;
    case 635: code635(p); break;
    case 636: code636(p); break;
    case 637: code637(p); break;
    case 638: code638(p); break;
    case 639: code639(p); break;
    case 640: code640(p); break;
    case 641: code641(p); break;
    case 642: code642(p); break;
    case 643: code643(p); break;
    case 644: code644(p); break;
    case 645: code645(p); break;
    case 646: code646(p); break;
    case 647: code647(p); break;
    case 648: code648(p); break;
    case 649: code649(p); break;
    case 650: code650(p); break;
    case 651: code651(p); break;
    case 652: code652(p); break;
    case 653: code653(p); break;
    case 654: code654(p); break;
    case 655: code655(p); break;
    case 656: code656(p); break;
    case 657: code657(p); break;
    case 658: code658(p); break;
    case 659: code659(p); break;
    case 660: code660(p); break;
    case 661: code661(p); break;
    case 662: code662(p); break;
    case 663: code663(p); break;
    default:
      throw new OptimizingCompilerException("BURS", "rule " + ruleno + " without emit code:",
        BURS_Debug.string[unsortedErnMap[ruleno]]);
    }
  }
}
