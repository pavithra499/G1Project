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
package org.jikesrvm;

import static org.jikesrvm.architecture.BootImageSize.*;
import org.vmmagic.unboxed.*;

/**
 * Constants defining heap layout constants
 */
public final class HeapLayoutConstants {

  /*
   * Determine the heap layout
   */
   
  /** The traditional 32-bit heap layout */
  public static final int HEAP_LAYOUT_32BIT = 1;

  /** The 64-bit heap layout that allows heap sizes up to 2^42 bytes */
  public static final int HEAP_LAYOUT_64BIT = 2;

  /** Choose between the possible heap layout styles */
  public static final int HEAP_LAYOUT = HEAP_LAYOUT_64BIT;

  /** The address of the start of the data section of the boot image. */
  public static final Address BOOT_IMAGE_DATA_START =
    Address.fromLong( 0x0000020000000000L );

  /** The address of the start of the code section of the boot image. */
  public static final Address BOOT_IMAGE_CODE_START =
    Address.fromLong( 0x0000020008000000L );

  /** The address of the start of the ref map section of the boot image. */
  public static final Address BOOT_IMAGE_RMAP_START =
    Address.fromLong( 0x000002000c000000L );

  /** The address in virtual memory that is the highest that can be mapped. */
  public static final Address MAXIMUM_MAPPABLE =
    Address.fromLong( 0x0000200000000000L );

  /** The current boot image data size */
  public static final int BOOT_IMAGE_DATA_SIZE = (BOOT_IMAGE_CODE_START.diff(BOOT_IMAGE_DATA_START).toInt());

  /** The current boot image code size */
  public static final int BOOT_IMAGE_CODE_SIZE = (BOOT_IMAGE_RMAP_START.diff(BOOT_IMAGE_CODE_START).toInt());

  /**
   * Limit for boot image data size: fail the build if
   * {@link org.jikesrvm.Configuration#AllowOversizedImages VM.AllowOversizedImages}
   * is not set and the boot image data size is greater than or equal to this amount
   * of bytes.
   */
  public static final int BOOT_IMAGE_DATA_SIZE_LIMIT = (int) (1.0f * (56 << 20) * dataSizeAdjustment());

  /**
   * Limit for boot image code size: fail the build if
   * {@link org.jikesrvm.Configuration#AllowOversizedImages VM.AllowOversizedImages}
   * is not set and the boot image code size is greater than or equal to this amount
   * of bytes.
   */
  public static final int BOOT_IMAGE_CODE_SIZE_LIMIT = (int) (1.0f * (24 << 20) * codeSizeAdjustment());

  /* Typical compression ratio is about 1/20 */
  public static final int BAD_MAP_COMPRESSION = 5;  // conservative heuristic
  public static final int MAX_BOOT_IMAGE_RMAP_SIZE = BOOT_IMAGE_DATA_SIZE/BAD_MAP_COMPRESSION;

  /** The address of the end of the data section of the boot image. */
  public static final Address BOOT_IMAGE_DATA_END = BOOT_IMAGE_DATA_START.plus(BOOT_IMAGE_DATA_SIZE);
  /** The address of the end of the code section of the boot image. */
  public static final Address BOOT_IMAGE_CODE_END = BOOT_IMAGE_CODE_START.plus(BOOT_IMAGE_CODE_SIZE);
  /** The address of the end of the ref map section of the boot image. */
  public static final Address BOOT_IMAGE_RMAP_END = BOOT_IMAGE_RMAP_START.plus(MAX_BOOT_IMAGE_RMAP_SIZE);
  /** The address of the end of the boot image. */
  public static final Address BOOT_IMAGE_END = BOOT_IMAGE_RMAP_END;

  private HeapLayoutConstants() {
    // prevent instantiation
  }

}
